%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UZ2rrv96ck

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:39 EST 2020

% Result     : Theorem 5.97s
% Output     : Refutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  177 (3764 expanded)
%              Number of leaves         :   38 (1166 expanded)
%              Depth                    :   28
%              Number of atoms          : 1524 (36221 expanded)
%              Number of equality atoms :   75 (2481 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t44_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_orders_2])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( ( k1_struct_0 @ X13 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('8',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    ! [X13: $i] :
      ( ( ( k1_struct_0 @ X13 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('11',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t43_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k1_orders_2 @ A @ ( k1_struct_0 @ A ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X26: $i] :
      ( ( ( k1_orders_2 @ X26 @ ( k1_struct_0 @ X26 ) )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t43_orders_2])).

thf('13',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','24'])).

thf('26',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('28',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

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

thf('29',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X21 @ X24 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X24 @ ( a_2_0_orders_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_A @ X1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

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

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_A @ X1 ) @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

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

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_orders_2 @ X19 @ X18 )
        = ( a_2_0_orders_2 @ X19 @ X18 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r2_orders_2 @ X16 @ X15 @ X17 )
      | ( X15 != X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ~ ( r2_orders_2 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X0 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r2_orders_2 @ sk_A @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('65',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('66',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( X24
        = ( sk_D @ X22 @ X21 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ ( a_2_0_orders_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['63','77'])).

thf('79',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('82',plain,(
    ~ ( r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['62','80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('84',plain,
    ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('85',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('87',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('88',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('89',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ( r2_orders_2 @ X21 @ X23 @ ( sk_D @ X22 @ X21 @ X24 ) )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( a_2_0_orders_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X2 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( a_2_0_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( a_2_0_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('96',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('97',plain,
    ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('98',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('103',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96','97','98','99','100','101','102','103'])).

thf('105',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','106'])).

thf('108',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('109',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('110',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('111',plain,(
    ! [X21: $i,X22: $i,X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r2_hidden @ X24 @ ( a_2_0_orders_2 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X21 ) )
      | ( X24 != X25 )
      | ( r2_hidden @ ( sk_E @ X25 @ X22 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('112',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ( r2_hidden @ ( sk_E @ X25 @ X22 @ X21 ) @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ X25 @ ( a_2_0_orders_2 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_struct_0 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('117',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('119',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('120',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','120'])).

thf('122',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','121','122','123','124','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('130',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('131',plain,
    ( ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('132',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('133',plain,(
    r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['107','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['82','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UZ2rrv96ck
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.97/6.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.97/6.18  % Solved by: fo/fo7.sh
% 5.97/6.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.97/6.18  % done 10758 iterations in 5.714s
% 5.97/6.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.97/6.18  % SZS output start Refutation
% 5.97/6.18  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.97/6.18  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 5.97/6.18  thf(sk_A_type, type, sk_A: $i).
% 5.97/6.18  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 5.97/6.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.97/6.18  thf(sk_B_type, type, sk_B: $i > $i).
% 5.97/6.18  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 5.97/6.18  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 5.97/6.18  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.97/6.18  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 5.97/6.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.97/6.18  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.97/6.18  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 5.97/6.18  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 5.97/6.18  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 5.97/6.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.97/6.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.97/6.18  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.97/6.18  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.97/6.18  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.97/6.18  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 5.97/6.18  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 5.97/6.18  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 5.97/6.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.97/6.18  thf(t29_mcart_1, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.97/6.18          ( ![B:$i]:
% 5.97/6.18            ( ~( ( r2_hidden @ B @ A ) & 
% 5.97/6.18                 ( ![C:$i,D:$i,E:$i]:
% 5.97/6.18                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 5.97/6.18                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 5.97/6.18  thf('0', plain,
% 5.97/6.18      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 5.97/6.18      inference('cnf', [status(esa)], [t29_mcart_1])).
% 5.97/6.18  thf(dt_k2_subset_1, axiom,
% 5.97/6.18    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.97/6.18  thf('1', plain,
% 5.97/6.18      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.97/6.18  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.97/6.18  thf('2', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 5.97/6.18      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.97/6.18  thf('3', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 5.97/6.18      inference('demod', [status(thm)], ['1', '2'])).
% 5.97/6.18  thf(t44_orders_2, conjecture,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.97/6.18         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.97/6.18       ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 5.97/6.18  thf(zf_stmt_0, negated_conjecture,
% 5.97/6.18    (~( ![A:$i]:
% 5.97/6.18        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.97/6.18            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.97/6.18          ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 5.97/6.18    inference('cnf.neg', [status(esa)], [t44_orders_2])).
% 5.97/6.18  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf(dt_l1_orders_2, axiom,
% 5.97/6.18    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 5.97/6.18  thf('5', plain, (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_orders_2 @ X20))),
% 5.97/6.18      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 5.97/6.18  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 5.97/6.18      inference('sup-', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf(d2_struct_0, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 5.97/6.18  thf('7', plain,
% 5.97/6.18      (![X13 : $i]:
% 5.97/6.18         (((k1_struct_0 @ X13) = (k1_xboole_0)) | ~ (l1_struct_0 @ X13))),
% 5.97/6.18      inference('cnf', [status(esa)], [d2_struct_0])).
% 5.97/6.18  thf('8', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['6', '7'])).
% 5.97/6.18  thf(d3_struct_0, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.97/6.18  thf('9', plain,
% 5.97/6.18      (![X14 : $i]:
% 5.97/6.18         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 5.97/6.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.97/6.18  thf('10', plain,
% 5.97/6.18      (![X13 : $i]:
% 5.97/6.18         (((k1_struct_0 @ X13) = (k1_xboole_0)) | ~ (l1_struct_0 @ X13))),
% 5.97/6.18      inference('cnf', [status(esa)], [d2_struct_0])).
% 5.97/6.18  thf('11', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['6', '7'])).
% 5.97/6.18  thf(t43_orders_2, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.97/6.18         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.97/6.18       ( ( k1_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ))).
% 5.97/6.18  thf('12', plain,
% 5.97/6.18      (![X26 : $i]:
% 5.97/6.18         (((k1_orders_2 @ X26 @ (k1_struct_0 @ X26)) = (u1_struct_0 @ X26))
% 5.97/6.18          | ~ (l1_orders_2 @ X26)
% 5.97/6.18          | ~ (v5_orders_2 @ X26)
% 5.97/6.18          | ~ (v4_orders_2 @ X26)
% 5.97/6.18          | ~ (v3_orders_2 @ X26)
% 5.97/6.18          | (v2_struct_0 @ X26))),
% 5.97/6.18      inference('cnf', [status(esa)], [t43_orders_2])).
% 5.97/6.18  thf('13', plain,
% 5.97/6.18      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 5.97/6.18        | (v2_struct_0 @ sk_A)
% 5.97/6.18        | ~ (v3_orders_2 @ sk_A)
% 5.97/6.18        | ~ (v4_orders_2 @ sk_A)
% 5.97/6.18        | ~ (v5_orders_2 @ sk_A)
% 5.97/6.18        | ~ (l1_orders_2 @ sk_A))),
% 5.97/6.18      inference('sup+', [status(thm)], ['11', '12'])).
% 5.97/6.18  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('18', plain,
% 5.97/6.18      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 5.97/6.18        | (v2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 5.97/6.18  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('20', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 5.97/6.18      inference('clc', [status(thm)], ['18', '19'])).
% 5.97/6.18  thf('21', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (((k1_orders_2 @ sk_A @ (k1_struct_0 @ X0)) = (u1_struct_0 @ sk_A))
% 5.97/6.18          | ~ (l1_struct_0 @ X0))),
% 5.97/6.18      inference('sup+', [status(thm)], ['10', '20'])).
% 5.97/6.18  thf('22', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (((k1_orders_2 @ sk_A @ (k1_struct_0 @ X0)) = (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (l1_struct_0 @ sk_A)
% 5.97/6.18          | ~ (l1_struct_0 @ X0))),
% 5.97/6.18      inference('sup+', [status(thm)], ['9', '21'])).
% 5.97/6.18  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 5.97/6.18      inference('sup-', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf('24', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (((k1_orders_2 @ sk_A @ (k1_struct_0 @ X0)) = (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (l1_struct_0 @ X0))),
% 5.97/6.18      inference('demod', [status(thm)], ['22', '23'])).
% 5.97/6.18  thf('25', plain,
% 5.97/6.18      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))
% 5.97/6.18        | ~ (l1_struct_0 @ sk_A))),
% 5.97/6.18      inference('sup+', [status(thm)], ['8', '24'])).
% 5.97/6.18  thf('26', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 5.97/6.18      inference('clc', [status(thm)], ['18', '19'])).
% 5.97/6.18  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 5.97/6.18      inference('sup-', [status(thm)], ['4', '5'])).
% 5.97/6.18  thf('28', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf(fraenkel_a_2_0_orders_2, axiom,
% 5.97/6.18    (![A:$i,B:$i,C:$i]:
% 5.97/6.18     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 5.97/6.18         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 5.97/6.18         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 5.97/6.18       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 5.97/6.18         ( ?[D:$i]:
% 5.97/6.18           ( ( ![E:$i]:
% 5.97/6.18               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 5.97/6.18                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 5.97/6.18             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 5.97/6.18  thf('29', plain,
% 5.97/6.18      (![X21 : $i, X22 : $i, X24 : $i]:
% 5.97/6.18         (~ (l1_orders_2 @ X21)
% 5.97/6.18          | ~ (v5_orders_2 @ X21)
% 5.97/6.18          | ~ (v4_orders_2 @ X21)
% 5.97/6.18          | ~ (v3_orders_2 @ X21)
% 5.97/6.18          | (v2_struct_0 @ X21)
% 5.97/6.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 5.97/6.18          | (m1_subset_1 @ (sk_D @ X22 @ X21 @ X24) @ (u1_struct_0 @ X21))
% 5.97/6.18          | ~ (r2_hidden @ X24 @ (a_2_0_orders_2 @ X21 @ X22)))),
% 5.97/6.18      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.97/6.18  thf('30', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.97/6.18          | ~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ sk_A @ X0))
% 5.97/6.18          | (m1_subset_1 @ (sk_D @ X0 @ sk_A @ X1) @ (u1_struct_0 @ sk_A))
% 5.97/6.18          | (v2_struct_0 @ sk_A)
% 5.97/6.18          | ~ (v3_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v4_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v5_orders_2 @ sk_A)
% 5.97/6.18          | ~ (l1_orders_2 @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['28', '29'])).
% 5.97/6.18  thf('31', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('33', plain, ((v4_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('36', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.97/6.18          | ~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ sk_A @ X0))
% 5.97/6.18          | (m1_subset_1 @ (sk_D @ X0 @ sk_A @ X1) @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | (v2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['30', '31', '32', '33', '34', '35'])).
% 5.97/6.18  thf('37', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((v2_struct_0 @ sk_A)
% 5.97/6.18          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 5.97/6.18             (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['3', '36'])).
% 5.97/6.18  thf('38', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 5.97/6.18      inference('demod', [status(thm)], ['1', '2'])).
% 5.97/6.18  thf('39', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf(d12_orders_2, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.97/6.18         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.97/6.18       ( ![B:$i]:
% 5.97/6.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.97/6.18           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 5.97/6.18  thf('40', plain,
% 5.97/6.18      (![X18 : $i, X19 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 5.97/6.18          | ((k1_orders_2 @ X19 @ X18) = (a_2_0_orders_2 @ X19 @ X18))
% 5.97/6.18          | ~ (l1_orders_2 @ X19)
% 5.97/6.18          | ~ (v5_orders_2 @ X19)
% 5.97/6.18          | ~ (v4_orders_2 @ X19)
% 5.97/6.18          | ~ (v3_orders_2 @ X19)
% 5.97/6.18          | (v2_struct_0 @ X19))),
% 5.97/6.18      inference('cnf', [status(esa)], [d12_orders_2])).
% 5.97/6.18  thf('41', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.97/6.18          | (v2_struct_0 @ sk_A)
% 5.97/6.18          | ~ (v3_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v4_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v5_orders_2 @ sk_A)
% 5.97/6.18          | ~ (l1_orders_2 @ sk_A)
% 5.97/6.18          | ((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['39', '40'])).
% 5.97/6.18  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('43', plain, ((v4_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('44', plain, ((v5_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('46', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.97/6.18          | (v2_struct_0 @ sk_A)
% 5.97/6.18          | ((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0)))),
% 5.97/6.18      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 5.97/6.18  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('48', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0))
% 5.97/6.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 5.97/6.18      inference('clc', [status(thm)], ['46', '47'])).
% 5.97/6.18  thf('49', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 5.97/6.18         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['38', '48'])).
% 5.97/6.18  thf('50', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         ((v2_struct_0 @ sk_A)
% 5.97/6.18          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 5.97/6.18             (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.97/6.18      inference('demod', [status(thm)], ['37', '49'])).
% 5.97/6.18  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('52', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.97/6.18          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 5.97/6.18             (k2_struct_0 @ sk_A)))),
% 5.97/6.18      inference('clc', [status(thm)], ['50', '51'])).
% 5.97/6.18  thf('53', plain,
% 5.97/6.18      ((((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 5.97/6.18        | (m1_subset_1 @ 
% 5.97/6.18           (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 5.97/6.18           (k2_struct_0 @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['0', '52'])).
% 5.97/6.18  thf('54', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('55', plain,
% 5.97/6.18      ((m1_subset_1 @ 
% 5.97/6.18        (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18         (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 5.97/6.18        (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 5.97/6.18  thf('56', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf(d10_orders_2, axiom,
% 5.97/6.18    (![A:$i]:
% 5.97/6.18     ( ( l1_orders_2 @ A ) =>
% 5.97/6.18       ( ![B:$i]:
% 5.97/6.18         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.97/6.18           ( ![C:$i]:
% 5.97/6.18             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.97/6.18               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 5.97/6.18                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 5.97/6.18  thf('57', plain,
% 5.97/6.18      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 5.97/6.18          | ~ (r2_orders_2 @ X16 @ X15 @ X17)
% 5.97/6.18          | ((X15) != (X17))
% 5.97/6.18          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 5.97/6.18          | ~ (l1_orders_2 @ X16))),
% 5.97/6.18      inference('cnf', [status(esa)], [d10_orders_2])).
% 5.97/6.18  thf('58', plain,
% 5.97/6.18      (![X16 : $i, X17 : $i]:
% 5.97/6.18         (~ (l1_orders_2 @ X16)
% 5.97/6.18          | ~ (r2_orders_2 @ X16 @ X17 @ X17)
% 5.97/6.18          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16)))),
% 5.97/6.18      inference('simplify', [status(thm)], ['57'])).
% 5.97/6.18  thf('59', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (r2_orders_2 @ sk_A @ X0 @ X0)
% 5.97/6.18          | ~ (l1_orders_2 @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['56', '58'])).
% 5.97/6.18  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('61', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (r2_orders_2 @ sk_A @ X0 @ X0))),
% 5.97/6.18      inference('demod', [status(thm)], ['59', '60'])).
% 5.97/6.18  thf('62', plain,
% 5.97/6.18      (~ (r2_orders_2 @ sk_A @ 
% 5.97/6.18          (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 5.97/6.18          (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['55', '61'])).
% 5.97/6.18  thf('63', plain,
% 5.97/6.18      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 5.97/6.18      inference('cnf', [status(esa)], [t29_mcart_1])).
% 5.97/6.18  thf('64', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('65', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 5.97/6.18      inference('demod', [status(thm)], ['1', '2'])).
% 5.97/6.18  thf('66', plain,
% 5.97/6.18      (![X21 : $i, X22 : $i, X24 : $i]:
% 5.97/6.18         (~ (l1_orders_2 @ X21)
% 5.97/6.18          | ~ (v5_orders_2 @ X21)
% 5.97/6.18          | ~ (v4_orders_2 @ X21)
% 5.97/6.18          | ~ (v3_orders_2 @ X21)
% 5.97/6.18          | (v2_struct_0 @ X21)
% 5.97/6.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 5.97/6.18          | ((X24) = (sk_D @ X22 @ X21 @ X24))
% 5.97/6.18          | ~ (r2_hidden @ X24 @ (a_2_0_orders_2 @ X21 @ X22)))),
% 5.97/6.18      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.97/6.18  thf('67', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.97/6.18          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.97/6.18          | (v2_struct_0 @ X0)
% 5.97/6.18          | ~ (v3_orders_2 @ X0)
% 5.97/6.18          | ~ (v4_orders_2 @ X0)
% 5.97/6.18          | ~ (v5_orders_2 @ X0)
% 5.97/6.18          | ~ (l1_orders_2 @ X0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['65', '66'])).
% 5.97/6.18  thf('68', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.97/6.18          | ~ (l1_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v5_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v4_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v3_orders_2 @ sk_A)
% 5.97/6.18          | (v2_struct_0 @ sk_A)
% 5.97/6.18          | ((X0) = (sk_D @ (u1_struct_0 @ sk_A) @ sk_A @ X0)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['64', '67'])).
% 5.97/6.18  thf('69', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 5.97/6.18         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['38', '48'])).
% 5.97/6.18  thf('70', plain, ((l1_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('71', plain, ((v5_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('72', plain, ((v4_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('73', plain, ((v3_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('74', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('75', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.97/6.18          | (v2_struct_0 @ sk_A)
% 5.97/6.18          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0)))),
% 5.97/6.18      inference('demod', [status(thm)],
% 5.97/6.18                ['68', '69', '70', '71', '72', '73', '74'])).
% 5.97/6.18  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('77', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 5.97/6.18          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.97/6.18      inference('clc', [status(thm)], ['75', '76'])).
% 5.97/6.18  thf('78', plain,
% 5.97/6.18      ((((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 5.97/6.18        | ((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.97/6.18            = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18               (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))))),
% 5.97/6.18      inference('sup-', [status(thm)], ['63', '77'])).
% 5.97/6.18  thf('79', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('80', plain,
% 5.97/6.18      (((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.97/6.18         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.97/6.18      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 5.97/6.18  thf('81', plain,
% 5.97/6.18      (((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.97/6.18         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.97/6.18      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 5.97/6.18  thf('82', plain,
% 5.97/6.18      (~ (r2_orders_2 @ sk_A @ 
% 5.97/6.18          (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18          (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.97/6.18      inference('demod', [status(thm)], ['62', '80', '81'])).
% 5.97/6.18  thf('83', plain,
% 5.97/6.18      ((m1_subset_1 @ 
% 5.97/6.18        (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18         (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 5.97/6.18        (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 5.97/6.18  thf('84', plain,
% 5.97/6.18      (((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.97/6.18         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.97/6.18      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 5.97/6.18  thf('85', plain,
% 5.97/6.18      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18        (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['83', '84'])).
% 5.97/6.18  thf('86', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('87', plain,
% 5.97/6.18      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 5.97/6.18      inference('cnf', [status(esa)], [t29_mcart_1])).
% 5.97/6.18  thf('88', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 5.97/6.18      inference('demod', [status(thm)], ['1', '2'])).
% 5.97/6.18  thf('89', plain,
% 5.97/6.18      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 5.97/6.18         (~ (l1_orders_2 @ X21)
% 5.97/6.18          | ~ (v5_orders_2 @ X21)
% 5.97/6.18          | ~ (v4_orders_2 @ X21)
% 5.97/6.18          | ~ (v3_orders_2 @ X21)
% 5.97/6.18          | (v2_struct_0 @ X21)
% 5.97/6.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 5.97/6.18          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 5.97/6.18          | (r2_orders_2 @ X21 @ X23 @ (sk_D @ X22 @ X21 @ X24))
% 5.97/6.18          | ~ (r2_hidden @ X23 @ X22)
% 5.97/6.18          | ~ (r2_hidden @ X24 @ (a_2_0_orders_2 @ X21 @ X22)))),
% 5.97/6.18      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.97/6.18  thf('90', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.97/6.18         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.97/6.18          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 5.97/6.18          | (r2_orders_2 @ X0 @ X2 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.97/6.18          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 5.97/6.18          | (v2_struct_0 @ X0)
% 5.97/6.18          | ~ (v3_orders_2 @ X0)
% 5.97/6.18          | ~ (v4_orders_2 @ X0)
% 5.97/6.18          | ~ (v5_orders_2 @ X0)
% 5.97/6.18          | ~ (l1_orders_2 @ X0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['88', '89'])).
% 5.97/6.18  thf('91', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 5.97/6.18          | ~ (l1_orders_2 @ X0)
% 5.97/6.18          | ~ (v5_orders_2 @ X0)
% 5.97/6.18          | ~ (v4_orders_2 @ X0)
% 5.97/6.18          | ~ (v3_orders_2 @ X0)
% 5.97/6.18          | (v2_struct_0 @ X0)
% 5.97/6.18          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.97/6.18          | (r2_orders_2 @ X0 @ X1 @ 
% 5.97/6.18             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.97/6.18              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 5.97/6.18          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['87', '90'])).
% 5.97/6.18  thf('92', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.97/6.18          | (r2_orders_2 @ sk_A @ X0 @ 
% 5.97/6.18             (sk_D @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18              (sk_B @ (a_2_0_orders_2 @ sk_A @ (u1_struct_0 @ sk_A)))))
% 5.97/6.18          | (v2_struct_0 @ sk_A)
% 5.97/6.18          | ~ (v3_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v4_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v5_orders_2 @ sk_A)
% 5.97/6.18          | ~ (l1_orders_2 @ sk_A)
% 5.97/6.18          | ((a_2_0_orders_2 @ sk_A @ (u1_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['86', '91'])).
% 5.97/6.18  thf('93', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('94', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('95', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('96', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 5.97/6.18         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['38', '48'])).
% 5.97/6.18  thf('97', plain,
% 5.97/6.18      (((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.97/6.18         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.97/6.18            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.97/6.18      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 5.97/6.18  thf('98', plain, ((v3_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('99', plain, ((v4_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('100', plain, ((v5_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('101', plain, ((l1_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('102', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('103', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 5.97/6.18         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['38', '48'])).
% 5.97/6.18  thf('104', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | (r2_orders_2 @ sk_A @ X0 @ 
% 5.97/6.18             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.97/6.18          | (v2_struct_0 @ sk_A)
% 5.97/6.18          | ((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 5.97/6.18      inference('demod', [status(thm)],
% 5.97/6.18                ['92', '93', '94', '95', '96', '97', '98', '99', '100', '101', 
% 5.97/6.18                 '102', '103'])).
% 5.97/6.18  thf('105', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('106', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | (r2_orders_2 @ sk_A @ X0 @ 
% 5.97/6.18             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.97/6.18          | (v2_struct_0 @ sk_A))),
% 5.97/6.18      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 5.97/6.18  thf('107', plain,
% 5.97/6.18      (((v2_struct_0 @ sk_A)
% 5.97/6.18        | (r2_orders_2 @ sk_A @ 
% 5.97/6.18           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.97/6.18        | ~ (r2_hidden @ 
% 5.97/6.18             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18             (k2_struct_0 @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['85', '106'])).
% 5.97/6.18  thf('108', plain,
% 5.97/6.18      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18        (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['83', '84'])).
% 5.97/6.18  thf('109', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf(t4_subset_1, axiom,
% 5.97/6.18    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.97/6.18  thf('110', plain,
% 5.97/6.18      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 5.97/6.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.97/6.18  thf('111', plain,
% 5.97/6.18      (![X21 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 5.97/6.18         (~ (l1_orders_2 @ X21)
% 5.97/6.18          | ~ (v5_orders_2 @ X21)
% 5.97/6.18          | ~ (v4_orders_2 @ X21)
% 5.97/6.18          | ~ (v3_orders_2 @ X21)
% 5.97/6.18          | (v2_struct_0 @ X21)
% 5.97/6.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 5.97/6.18          | (r2_hidden @ X24 @ (a_2_0_orders_2 @ X21 @ X22))
% 5.97/6.18          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X21))
% 5.97/6.18          | ((X24) != (X25))
% 5.97/6.18          | (r2_hidden @ (sk_E @ X25 @ X22 @ X21) @ X22))),
% 5.97/6.18      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.97/6.18  thf('112', plain,
% 5.97/6.18      (![X21 : $i, X22 : $i, X25 : $i]:
% 5.97/6.18         ((r2_hidden @ (sk_E @ X25 @ X22 @ X21) @ X22)
% 5.97/6.18          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X21))
% 5.97/6.18          | (r2_hidden @ X25 @ (a_2_0_orders_2 @ X21 @ X22))
% 5.97/6.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 5.97/6.18          | (v2_struct_0 @ X21)
% 5.97/6.18          | ~ (v3_orders_2 @ X21)
% 5.97/6.18          | ~ (v4_orders_2 @ X21)
% 5.97/6.18          | ~ (v5_orders_2 @ X21)
% 5.97/6.18          | ~ (l1_orders_2 @ X21))),
% 5.97/6.18      inference('simplify', [status(thm)], ['111'])).
% 5.97/6.18  thf('113', plain,
% 5.97/6.18      (![X0 : $i, X1 : $i]:
% 5.97/6.18         (~ (l1_orders_2 @ X0)
% 5.97/6.18          | ~ (v5_orders_2 @ X0)
% 5.97/6.18          | ~ (v4_orders_2 @ X0)
% 5.97/6.18          | ~ (v3_orders_2 @ X0)
% 5.97/6.18          | (v2_struct_0 @ X0)
% 5.97/6.18          | (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ k1_xboole_0))
% 5.97/6.18          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.97/6.18          | (r2_hidden @ (sk_E @ X1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['110', '112'])).
% 5.97/6.18  thf('114', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 5.97/6.18          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ k1_xboole_0))
% 5.97/6.18          | (v2_struct_0 @ sk_A)
% 5.97/6.18          | ~ (v3_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v4_orders_2 @ sk_A)
% 5.97/6.18          | ~ (v5_orders_2 @ sk_A)
% 5.97/6.18          | ~ (l1_orders_2 @ sk_A))),
% 5.97/6.18      inference('sup-', [status(thm)], ['109', '113'])).
% 5.97/6.18  thf('115', plain,
% 5.97/6.18      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 5.97/6.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.97/6.18  thf('116', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0))
% 5.97/6.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 5.97/6.18      inference('clc', [status(thm)], ['46', '47'])).
% 5.97/6.18  thf('117', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ k1_xboole_0)
% 5.97/6.18         = (a_2_0_orders_2 @ sk_A @ k1_xboole_0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['115', '116'])).
% 5.97/6.18  thf('118', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 5.97/6.18      inference('clc', [status(thm)], ['18', '19'])).
% 5.97/6.18  thf('119', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 5.97/6.18  thf('120', plain,
% 5.97/6.18      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['118', '119'])).
% 5.97/6.18  thf('121', plain,
% 5.97/6.18      (((k2_struct_0 @ sk_A) = (a_2_0_orders_2 @ sk_A @ k1_xboole_0))),
% 5.97/6.18      inference('demod', [status(thm)], ['117', '120'])).
% 5.97/6.18  thf('122', plain, ((v3_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('123', plain, ((v4_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('124', plain, ((v5_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('125', plain, ((l1_orders_2 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('126', plain,
% 5.97/6.18      (![X0 : $i]:
% 5.97/6.18         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 5.97/6.18          | (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 5.97/6.18          | (v2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)],
% 5.97/6.18                ['114', '121', '122', '123', '124', '125'])).
% 5.97/6.18  thf('127', plain,
% 5.97/6.18      (((v2_struct_0 @ sk_A)
% 5.97/6.18        | (r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18           (k2_struct_0 @ sk_A))
% 5.97/6.18        | (r2_hidden @ 
% 5.97/6.18           (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18            k1_xboole_0 @ sk_A) @ 
% 5.97/6.18           k1_xboole_0))),
% 5.97/6.18      inference('sup-', [status(thm)], ['108', '126'])).
% 5.97/6.18  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('129', plain,
% 5.97/6.18      (((r2_hidden @ 
% 5.97/6.18         (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18          k1_xboole_0 @ sk_A) @ 
% 5.97/6.18         k1_xboole_0)
% 5.97/6.18        | (r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18           (k2_struct_0 @ sk_A)))),
% 5.97/6.18      inference('clc', [status(thm)], ['127', '128'])).
% 5.97/6.18  thf(t7_ordinal1, axiom,
% 5.97/6.18    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.97/6.18  thf('130', plain,
% 5.97/6.18      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 5.97/6.18      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.97/6.18  thf('131', plain,
% 5.97/6.18      (((r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18         (k2_struct_0 @ sk_A))
% 5.97/6.18        | ~ (r1_tarski @ k1_xboole_0 @ 
% 5.97/6.18             (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18              k1_xboole_0 @ sk_A)))),
% 5.97/6.18      inference('sup-', [status(thm)], ['129', '130'])).
% 5.97/6.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.97/6.18  thf('132', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.97/6.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.97/6.18  thf('133', plain,
% 5.97/6.18      ((r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18        (k2_struct_0 @ sk_A))),
% 5.97/6.18      inference('demod', [status(thm)], ['131', '132'])).
% 5.97/6.18  thf('134', plain,
% 5.97/6.18      (((v2_struct_0 @ sk_A)
% 5.97/6.18        | (r2_orders_2 @ sk_A @ 
% 5.97/6.18           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.97/6.18      inference('demod', [status(thm)], ['107', '133'])).
% 5.97/6.18  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 5.97/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.97/6.18  thf('136', plain,
% 5.97/6.18      ((r2_orders_2 @ sk_A @ 
% 5.97/6.18        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.97/6.18        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.97/6.18      inference('clc', [status(thm)], ['134', '135'])).
% 5.97/6.18  thf('137', plain, ($false), inference('demod', [status(thm)], ['82', '136'])).
% 5.97/6.18  
% 5.97/6.18  % SZS output end Refutation
% 5.97/6.18  
% 5.97/6.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
