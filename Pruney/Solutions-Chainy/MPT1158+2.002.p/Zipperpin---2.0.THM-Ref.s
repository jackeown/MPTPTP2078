%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SEjQGEy33A

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:58 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 896 expanded)
%              Number of leaves         :   30 ( 265 expanded)
%              Depth                    :   37
%              Number of atoms          : 1634 (16740 expanded)
%              Number of equality atoms :   33 ( 129 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r2_hidden @ X13 @ ( a_2_1_orders_2 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X10 ) )
      | ( X13 != X14 )
      | ( r2_hidden @ ( sk_E @ X14 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_E @ X14 @ X11 @ X10 ) @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v2_struct_0 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

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

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k2_orders_2 @ X8 @ X7 )
        = ( a_2_1_orders_2 @ X8 @ X7 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('36',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('37',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X13
        = ( sk_D @ X11 @ X10 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( a_2_1_orders_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( X0
        = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('43',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( X0
        = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B
      = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,
    ( ( ( sk_B
        = ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['36','50'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('55',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('56',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('58',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('60',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ( r2_orders_2 @ X10 @ ( sk_D @ X11 @ X10 @ X13 ) @ X12 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( a_2_1_orders_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C_1 ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ X0 ) @ X1 )
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
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C_1 ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['51','75'])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('80',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('83',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['35','87'])).

thf('89',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['34','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['32','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','92'])).

thf('94',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('97',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('100',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r2_hidden @ X13 @ ( a_2_1_orders_2 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X10 ) )
      | ( X13 != X14 )
      | ~ ( r2_orders_2 @ X10 @ X14 @ ( sk_E @ X14 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('101',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ~ ( r2_orders_2 @ X10 @ X14 @ ( sk_E @ X14 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v2_struct_0 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C_1 ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','107'])).

thf('109',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['37'])).

thf('110',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('111',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['35','87','110'])).

thf('112',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['109','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','112','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('119',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('120',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['35','87'])).

thf('122',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['120','121'])).

thf('123',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['117','122'])).

thf('124',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('127',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['0','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SEjQGEy33A
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 10:09:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.59/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.81  % Solved by: fo/fo7.sh
% 0.59/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.81  % done 668 iterations in 0.334s
% 0.59/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.81  % SZS output start Refutation
% 0.59/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.81  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.59/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.81  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.59/0.81  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.59/0.81  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.81  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.59/0.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.81  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.59/0.81  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.81  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.59/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.81  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.81  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.59/0.81  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.59/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.81  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.59/0.81  thf(t52_orders_2, conjecture,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.81         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.81           ( ![C:$i]:
% 0.59/0.81             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.81               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.59/0.81                 ( r2_hidden @
% 0.59/0.81                   B @ 
% 0.59/0.81                   ( k2_orders_2 @
% 0.59/0.81                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.81    (~( ![A:$i]:
% 0.59/0.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.81            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.81          ( ![B:$i]:
% 0.59/0.81            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.81              ( ![C:$i]:
% 0.59/0.81                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.81                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.59/0.81                    ( r2_hidden @
% 0.59/0.81                      B @ 
% 0.59/0.81                      ( k2_orders_2 @
% 0.59/0.81                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 0.59/0.81  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(redefinition_k6_domain_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.59/0.81       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (![X15 : $i, X16 : $i]:
% 0.59/0.81         ((v1_xboole_0 @ X15)
% 0.59/0.81          | ~ (m1_subset_1 @ X16 @ X15)
% 0.59/0.81          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.59/0.81  thf('3', plain,
% 0.59/0.81      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.59/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf('4', plain,
% 0.59/0.81      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.59/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('6', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(t35_orders_2, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.81           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.59/0.81             ( m1_subset_1 @
% 0.59/0.81               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.59/0.81               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.59/0.81  thf('7', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.59/0.81          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X17) @ 
% 0.59/0.81             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.81          | ~ (l1_orders_2 @ X18)
% 0.59/0.81          | ~ (v3_orders_2 @ X18)
% 0.59/0.81          | (v2_struct_0 @ X18))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.59/0.81  thf('8', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_A)
% 0.59/0.81        | ~ (v3_orders_2 @ sk_A)
% 0.59/0.81        | ~ (l1_orders_2 @ sk_A)
% 0.59/0.81        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.59/0.81           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.81  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_A)
% 0.59/0.81        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.59/0.81           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.81      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.59/0.81  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('clc', [status(thm)], ['11', '12'])).
% 0.59/0.81  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.59/0.81         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.59/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.59/0.81       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.59/0.81         ( ?[D:$i]:
% 0.59/0.81           ( ( ![E:$i]:
% 0.59/0.81               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.59/0.81                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.59/0.81             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.59/0.81         (~ (l1_orders_2 @ X10)
% 0.59/0.81          | ~ (v5_orders_2 @ X10)
% 0.59/0.81          | ~ (v4_orders_2 @ X10)
% 0.59/0.81          | ~ (v3_orders_2 @ X10)
% 0.59/0.81          | (v2_struct_0 @ X10)
% 0.59/0.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.59/0.81          | (r2_hidden @ X13 @ (a_2_1_orders_2 @ X10 @ X11))
% 0.59/0.81          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X10))
% 0.59/0.81          | ((X13) != (X14))
% 0.59/0.81          | (r2_hidden @ (sk_E @ X14 @ X11 @ X10) @ X11))),
% 0.59/0.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i, X14 : $i]:
% 0.59/0.81         ((r2_hidden @ (sk_E @ X14 @ X11 @ X10) @ X11)
% 0.59/0.81          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X10))
% 0.59/0.81          | (r2_hidden @ X14 @ (a_2_1_orders_2 @ X10 @ X11))
% 0.59/0.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.59/0.81          | (v2_struct_0 @ X10)
% 0.59/0.81          | ~ (v3_orders_2 @ X10)
% 0.59/0.81          | ~ (v4_orders_2 @ X10)
% 0.59/0.81          | ~ (v5_orders_2 @ X10)
% 0.59/0.81          | ~ (l1_orders_2 @ X10))),
% 0.59/0.81      inference('simplify', [status(thm)], ['14'])).
% 0.59/0.81  thf('16', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (l1_orders_2 @ sk_A)
% 0.59/0.81          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.81          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.81          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | (r2_hidden @ X0 @ 
% 0.59/0.81             (a_2_1_orders_2 @ sk_A @ 
% 0.59/0.81              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.81          | (r2_hidden @ 
% 0.59/0.81             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.59/0.81             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['13', '15'])).
% 0.59/0.81  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('18', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('21', plain,
% 0.59/0.81      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('clc', [status(thm)], ['11', '12'])).
% 0.59/0.81  thf(d13_orders_2, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.81         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.59/0.81  thf('22', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.59/0.81          | ((k2_orders_2 @ X8 @ X7) = (a_2_1_orders_2 @ X8 @ X7))
% 0.59/0.81          | ~ (l1_orders_2 @ X8)
% 0.59/0.81          | ~ (v5_orders_2 @ X8)
% 0.59/0.81          | ~ (v4_orders_2 @ X8)
% 0.59/0.81          | ~ (v3_orders_2 @ X8)
% 0.59/0.81          | (v2_struct_0 @ X8))),
% 0.59/0.81      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.59/0.81  thf('23', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_A)
% 0.59/0.81        | ~ (v3_orders_2 @ sk_A)
% 0.59/0.81        | ~ (v4_orders_2 @ sk_A)
% 0.59/0.81        | ~ (v5_orders_2 @ sk_A)
% 0.59/0.81        | ~ (l1_orders_2 @ sk_A)
% 0.59/0.81        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.81            = (a_2_1_orders_2 @ sk_A @ 
% 0.59/0.81               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['21', '22'])).
% 0.59/0.81  thf('24', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('25', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('28', plain,
% 0.59/0.81      (((v2_struct_0 @ sk_A)
% 0.59/0.81        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.81            = (a_2_1_orders_2 @ sk_A @ 
% 0.59/0.81               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.59/0.81      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.59/0.81  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.81         = (a_2_1_orders_2 @ sk_A @ 
% 0.59/0.81            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.59/0.81      inference('clc', [status(thm)], ['28', '29'])).
% 0.59/0.81  thf('31', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((v2_struct_0 @ sk_A)
% 0.59/0.81          | (r2_hidden @ X0 @ 
% 0.59/0.81             (k2_orders_2 @ sk_A @ 
% 0.59/0.81              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.81          | (r2_hidden @ 
% 0.59/0.81             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.59/0.81             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.59/0.81      inference('demod', [status(thm)], ['16', '17', '18', '19', '20', '30'])).
% 0.59/0.81  thf('32', plain,
% 0.59/0.81      (((r2_hidden @ 
% 0.59/0.81         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.59/0.81         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.81        | (r2_hidden @ sk_B @ 
% 0.59/0.81           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.59/0.81        | (v2_struct_0 @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['5', '31'])).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      ((~ (r2_hidden @ sk_B @ 
% 0.59/0.81           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.59/0.81        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      ((~ (r2_hidden @ sk_B @ 
% 0.59/0.81           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.59/0.81         <= (~
% 0.59/0.81             ((r2_hidden @ sk_B @ 
% 0.59/0.81               (k2_orders_2 @ sk_A @ 
% 0.59/0.81                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.81      inference('split', [status(esa)], ['33'])).
% 0.59/0.81  thf('35', plain,
% 0.59/0.81      (~
% 0.59/0.81       ((r2_hidden @ sk_B @ 
% 0.59/0.81         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))) | 
% 0.59/0.81       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.59/0.81      inference('split', [status(esa)], ['33'])).
% 0.59/0.81  thf('36', plain,
% 0.59/0.81      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.59/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf('37', plain,
% 0.59/0.81      (((r2_hidden @ sk_B @ 
% 0.59/0.81         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.59/0.81        | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('38', plain,
% 0.59/0.81      (((r2_hidden @ sk_B @ 
% 0.59/0.81         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.59/0.81         <= (((r2_hidden @ sk_B @ 
% 0.59/0.81               (k2_orders_2 @ sk_A @ 
% 0.59/0.81                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.81      inference('split', [status(esa)], ['37'])).
% 0.59/0.81  thf('39', plain,
% 0.59/0.81      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('clc', [status(thm)], ['11', '12'])).
% 0.59/0.81  thf('40', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.59/0.81         (~ (l1_orders_2 @ X10)
% 0.59/0.81          | ~ (v5_orders_2 @ X10)
% 0.59/0.81          | ~ (v4_orders_2 @ X10)
% 0.59/0.81          | ~ (v3_orders_2 @ X10)
% 0.59/0.81          | (v2_struct_0 @ X10)
% 0.59/0.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.59/0.81          | ((X13) = (sk_D @ X11 @ X10 @ X13))
% 0.59/0.81          | ~ (r2_hidden @ X13 @ (a_2_1_orders_2 @ X10 @ X11)))),
% 0.59/0.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.59/0.81  thf('41', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (r2_hidden @ X0 @ 
% 0.59/0.81             (a_2_1_orders_2 @ sk_A @ 
% 0.59/0.81              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.59/0.81          | ((X0)
% 0.59/0.81              = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ 
% 0.59/0.81                 X0))
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.81          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.81          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.81          | ~ (l1_orders_2 @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('42', plain,
% 0.59/0.81      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.81         = (a_2_1_orders_2 @ sk_A @ 
% 0.59/0.81            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.59/0.81      inference('clc', [status(thm)], ['28', '29'])).
% 0.59/0.81  thf('43', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('44', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('45', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('46', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('47', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (r2_hidden @ X0 @ 
% 0.59/0.81             (k2_orders_2 @ sk_A @ 
% 0.59/0.81              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.59/0.81          | ((X0)
% 0.59/0.81              = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ 
% 0.59/0.81                 X0))
% 0.59/0.81          | (v2_struct_0 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '46'])).
% 0.59/0.81  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('49', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((X0)
% 0.59/0.81            = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ X0))
% 0.59/0.81          | ~ (r2_hidden @ X0 @ 
% 0.59/0.81               (k2_orders_2 @ sk_A @ 
% 0.59/0.81                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.59/0.81      inference('clc', [status(thm)], ['47', '48'])).
% 0.59/0.81  thf('50', plain,
% 0.59/0.81      ((((sk_B)
% 0.59/0.81          = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ sk_B)))
% 0.59/0.81         <= (((r2_hidden @ sk_B @ 
% 0.59/0.81               (k2_orders_2 @ sk_A @ 
% 0.59/0.81                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['38', '49'])).
% 0.59/0.81  thf('51', plain,
% 0.59/0.81      (((((sk_B) = (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B))
% 0.59/0.81         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= (((r2_hidden @ sk_B @ 
% 0.59/0.81               (k2_orders_2 @ sk_A @ 
% 0.59/0.81                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['36', '50'])).
% 0.59/0.81  thf(d1_tarski, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.59/0.81  thf('52', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.81  thf('53', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.81      inference('simplify', [status(thm)], ['52'])).
% 0.59/0.81  thf('54', plain,
% 0.59/0.81      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.59/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf('55', plain,
% 0.59/0.81      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.81         = (a_2_1_orders_2 @ sk_A @ 
% 0.59/0.81            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.59/0.81      inference('clc', [status(thm)], ['28', '29'])).
% 0.59/0.81  thf('56', plain,
% 0.59/0.81      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.81          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['54', '55'])).
% 0.59/0.81  thf('57', plain,
% 0.59/0.81      (((r2_hidden @ sk_B @ 
% 0.59/0.81         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.59/0.81         <= (((r2_hidden @ sk_B @ 
% 0.59/0.81               (k2_orders_2 @ sk_A @ 
% 0.59/0.81                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.81      inference('split', [status(esa)], ['37'])).
% 0.59/0.81  thf('58', plain,
% 0.59/0.81      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.81         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= (((r2_hidden @ sk_B @ 
% 0.59/0.81               (k2_orders_2 @ sk_A @ 
% 0.59/0.81                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['56', '57'])).
% 0.59/0.81  thf('59', plain,
% 0.59/0.81      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.59/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf('60', plain,
% 0.59/0.81      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('clc', [status(thm)], ['11', '12'])).
% 0.59/0.81  thf('61', plain,
% 0.59/0.81      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.59/0.81         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['59', '60'])).
% 0.59/0.81  thf('62', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.81         (~ (l1_orders_2 @ X10)
% 0.59/0.81          | ~ (v5_orders_2 @ X10)
% 0.59/0.81          | ~ (v4_orders_2 @ X10)
% 0.59/0.81          | ~ (v3_orders_2 @ X10)
% 0.59/0.81          | (v2_struct_0 @ X10)
% 0.59/0.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.59/0.81          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.59/0.81          | (r2_orders_2 @ X10 @ (sk_D @ X11 @ X10 @ X13) @ X12)
% 0.59/0.81          | ~ (r2_hidden @ X12 @ X11)
% 0.59/0.81          | ~ (r2_hidden @ X13 @ (a_2_1_orders_2 @ X10 @ X11)))),
% 0.59/0.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.59/0.81  thf('63', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.81          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.81          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C_1))
% 0.59/0.81          | (r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ X0) @ 
% 0.59/0.81             X1)
% 0.59/0.81          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.81          | (v2_struct_0 @ sk_A)
% 0.59/0.81          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.81          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.81          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.81          | ~ (l1_orders_2 @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['61', '62'])).
% 0.59/0.81  thf('64', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('65', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('66', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('68', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.81          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.81          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C_1))
% 0.59/0.81          | (r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ X0) @ 
% 0.59/0.81             X1)
% 0.59/0.81          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.81          | (v2_struct_0 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.59/0.81  thf('69', plain,
% 0.59/0.81      ((![X0 : $i]:
% 0.59/0.81          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.81           | (v2_struct_0 @ sk_A)
% 0.59/0.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.81           | (r2_orders_2 @ sk_A @ 
% 0.59/0.82              (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ X0)
% 0.59/0.82           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.59/0.82           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.82         <= (((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['58', '68'])).
% 0.59/0.82  thf('70', plain,
% 0.59/0.82      ((![X0 : $i]:
% 0.59/0.82          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.59/0.82           | (r2_orders_2 @ sk_A @ 
% 0.59/0.82              (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ X0)
% 0.59/0.82           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82           | (v2_struct_0 @ sk_A)
% 0.59/0.82           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.82         <= (((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['69'])).
% 0.59/0.82  thf('71', plain,
% 0.59/0.82      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82         | (v2_struct_0 @ sk_A)
% 0.59/0.82         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.59/0.82         | (r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ 
% 0.59/0.82            sk_C_1)))
% 0.59/0.82         <= (((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['53', '70'])).
% 0.59/0.82  thf('72', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('73', plain,
% 0.59/0.82      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82         | (v2_struct_0 @ sk_A)
% 0.59/0.82         | (r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ 
% 0.59/0.82            sk_C_1)))
% 0.59/0.82         <= (((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('demod', [status(thm)], ['71', '72'])).
% 0.59/0.82  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('75', plain,
% 0.59/0.82      ((((r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ 
% 0.59/0.82          sk_C_1)
% 0.59/0.82         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.82         <= (((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('clc', [status(thm)], ['73', '74'])).
% 0.59/0.82  thf('76', plain,
% 0.59/0.82      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.59/0.82         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.82         <= (((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('sup+', [status(thm)], ['51', '75'])).
% 0.59/0.82  thf('77', plain,
% 0.59/0.82      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82         | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.82         <= (((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('simplify', [status(thm)], ['76'])).
% 0.59/0.82  thf('78', plain,
% 0.59/0.82      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.59/0.82         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.59/0.82      inference('split', [status(esa)], ['33'])).
% 0.59/0.82  thf('79', plain,
% 0.59/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.59/0.82             ((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['77', '78'])).
% 0.59/0.82  thf(fc2_struct_0, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.59/0.82       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.82  thf('80', plain,
% 0.59/0.82      (![X6 : $i]:
% 0.59/0.82         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.59/0.82          | ~ (l1_struct_0 @ X6)
% 0.59/0.82          | (v2_struct_0 @ X6))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.82  thf('81', plain,
% 0.59/0.82      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.59/0.82         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.59/0.82             ((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['79', '80'])).
% 0.59/0.82  thf('82', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(dt_l1_orders_2, axiom,
% 0.59/0.82    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.82  thf('83', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_orders_2 @ X9))),
% 0.59/0.82      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.59/0.82  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.82      inference('sup-', [status(thm)], ['82', '83'])).
% 0.59/0.82  thf('85', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A))
% 0.59/0.82         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.59/0.82             ((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('demod', [status(thm)], ['81', '84'])).
% 0.59/0.82  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('87', plain,
% 0.59/0.82      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.59/0.82       ~
% 0.59/0.82       ((r2_hidden @ sk_B @ 
% 0.59/0.82         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['85', '86'])).
% 0.59/0.82  thf('88', plain,
% 0.59/0.82      (~
% 0.59/0.82       ((r2_hidden @ sk_B @ 
% 0.59/0.82         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['35', '87'])).
% 0.59/0.82  thf('89', plain,
% 0.59/0.82      (~ (r2_hidden @ sk_B @ 
% 0.59/0.82          (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['34', '88'])).
% 0.59/0.82  thf('90', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A)
% 0.59/0.82        | (r2_hidden @ 
% 0.59/0.82           (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.59/0.82           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.59/0.82      inference('clc', [status(thm)], ['32', '89'])).
% 0.59/0.82  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('92', plain,
% 0.59/0.82      ((r2_hidden @ 
% 0.59/0.82        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.59/0.82        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.59/0.82      inference('clc', [status(thm)], ['90', '91'])).
% 0.59/0.82  thf('93', plain,
% 0.59/0.82      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.59/0.82         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['4', '92'])).
% 0.59/0.82  thf('94', plain,
% 0.59/0.82      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.59/0.82         (k1_tarski @ sk_C_1))
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['3', '93'])).
% 0.59/0.82  thf('95', plain,
% 0.59/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82        | (r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.59/0.82           (k1_tarski @ sk_C_1)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['94'])).
% 0.59/0.82  thf('96', plain,
% 0.59/0.82      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.59/0.82      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.82  thf('97', plain,
% 0.59/0.82      (![X0 : $i, X3 : $i]:
% 0.59/0.82         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['96'])).
% 0.59/0.82  thf('98', plain,
% 0.59/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82        | ((sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) = (sk_C_1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['95', '97'])).
% 0.59/0.82  thf('99', plain,
% 0.59/0.82      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.59/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['59', '60'])).
% 0.59/0.82  thf('100', plain,
% 0.59/0.82      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.59/0.82         (~ (l1_orders_2 @ X10)
% 0.59/0.82          | ~ (v5_orders_2 @ X10)
% 0.59/0.82          | ~ (v4_orders_2 @ X10)
% 0.59/0.82          | ~ (v3_orders_2 @ X10)
% 0.59/0.82          | (v2_struct_0 @ X10)
% 0.59/0.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.59/0.82          | (r2_hidden @ X13 @ (a_2_1_orders_2 @ X10 @ X11))
% 0.59/0.82          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X10))
% 0.59/0.82          | ((X13) != (X14))
% 0.59/0.82          | ~ (r2_orders_2 @ X10 @ X14 @ (sk_E @ X14 @ X11 @ X10)))),
% 0.59/0.82      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.59/0.82  thf('101', plain,
% 0.59/0.82      (![X10 : $i, X11 : $i, X14 : $i]:
% 0.59/0.82         (~ (r2_orders_2 @ X10 @ X14 @ (sk_E @ X14 @ X11 @ X10))
% 0.59/0.82          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X10))
% 0.59/0.82          | (r2_hidden @ X14 @ (a_2_1_orders_2 @ X10 @ X11))
% 0.59/0.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.59/0.82          | (v2_struct_0 @ X10)
% 0.59/0.82          | ~ (v3_orders_2 @ X10)
% 0.59/0.82          | ~ (v4_orders_2 @ X10)
% 0.59/0.82          | ~ (v5_orders_2 @ X10)
% 0.59/0.82          | ~ (l1_orders_2 @ X10))),
% 0.59/0.82      inference('simplify', [status(thm)], ['100'])).
% 0.59/0.82  thf('102', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82          | ~ (l1_orders_2 @ sk_A)
% 0.59/0.82          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.82          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.82          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.82          | (v2_struct_0 @ sk_A)
% 0.59/0.82          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.59/0.82               (sk_E @ X0 @ (k1_tarski @ sk_C_1) @ sk_A)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['99', '101'])).
% 0.59/0.82  thf('103', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('104', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('105', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('106', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('107', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82          | (v2_struct_0 @ sk_A)
% 0.59/0.82          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.59/0.82               (sk_E @ X0 @ (k1_tarski @ sk_C_1) @ sk_A)))),
% 0.59/0.82      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.59/0.82  thf('108', plain,
% 0.59/0.82      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.59/0.82        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.82        | (v2_struct_0 @ sk_A)
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['98', '107'])).
% 0.59/0.82  thf('109', plain,
% 0.59/0.82      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.59/0.82         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.59/0.82      inference('split', [status(esa)], ['37'])).
% 0.59/0.82  thf('110', plain,
% 0.59/0.82      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.59/0.82       ((r2_hidden @ sk_B @ 
% 0.59/0.82         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.59/0.82      inference('split', [status(esa)], ['37'])).
% 0.59/0.82  thf('111', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['35', '87', '110'])).
% 0.59/0.82  thf('112', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['109', '111'])).
% 0.59/0.82  thf('113', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('114', plain,
% 0.59/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.82        | (v2_struct_0 @ sk_A)
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('demod', [status(thm)], ['108', '112', '113'])).
% 0.59/0.82  thf('115', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A)
% 0.59/0.82        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['114'])).
% 0.59/0.82  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('117', plain,
% 0.59/0.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.82        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1))))),
% 0.59/0.82      inference('clc', [status(thm)], ['115', '116'])).
% 0.59/0.82  thf('118', plain,
% 0.59/0.82      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.59/0.82          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('sup+', [status(thm)], ['54', '55'])).
% 0.59/0.82  thf('119', plain,
% 0.59/0.82      ((~ (r2_hidden @ sk_B @ 
% 0.59/0.82           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.59/0.82         <= (~
% 0.59/0.82             ((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('split', [status(esa)], ['33'])).
% 0.59/0.82  thf('120', plain,
% 0.59/0.82      (((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.82         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.82         <= (~
% 0.59/0.82             ((r2_hidden @ sk_B @ 
% 0.59/0.82               (k2_orders_2 @ sk_A @ 
% 0.59/0.82                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['118', '119'])).
% 0.59/0.82  thf('121', plain,
% 0.59/0.82      (~
% 0.59/0.82       ((r2_hidden @ sk_B @ 
% 0.59/0.82         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.59/0.82      inference('sat_resolution*', [status(thm)], ['35', '87'])).
% 0.59/0.82  thf('122', plain,
% 0.59/0.82      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.59/0.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.82      inference('simpl_trail', [status(thm)], ['120', '121'])).
% 0.59/0.82  thf('123', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.59/0.82      inference('clc', [status(thm)], ['117', '122'])).
% 0.59/0.82  thf('124', plain,
% 0.59/0.82      (![X6 : $i]:
% 0.59/0.82         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.59/0.82          | ~ (l1_struct_0 @ X6)
% 0.59/0.82          | (v2_struct_0 @ X6))),
% 0.59/0.82      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.82  thf('125', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['123', '124'])).
% 0.59/0.82  thf('126', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.82      inference('sup-', [status(thm)], ['82', '83'])).
% 0.59/0.82  thf('127', plain, ((v2_struct_0 @ sk_A)),
% 0.59/0.82      inference('demod', [status(thm)], ['125', '126'])).
% 0.59/0.82  thf('128', plain, ($false), inference('demod', [status(thm)], ['0', '127'])).
% 0.59/0.82  
% 0.59/0.82  % SZS output end Refutation
% 0.59/0.82  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
