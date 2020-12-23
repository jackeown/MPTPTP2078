%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TjlcRkIjQC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:41 EST 2020

% Result     : Theorem 5.49s
% Output     : Refutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :  200 (5757 expanded)
%              Number of leaves         :   41 (1761 expanded)
%              Depth                    :   28
%              Number of atoms          : 1809 (58510 expanded)
%              Number of equality atoms :   72 (3910 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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

thf('1',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X19: $i] :
      ( ( ( k1_struct_0 @ X19 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('5',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t43_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k1_orders_2 @ A @ ( k1_struct_0 @ A ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X39: $i] :
      ( ( ( k1_orders_2 @ X39 @ ( k1_struct_0 @ X39 ) )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 )
      | ~ ( v5_orders_2 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v3_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t43_orders_2])).

thf('7',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('17',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('19',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X26 @ X25 @ X28 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X28 @ ( a_2_0_orders_2 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('28',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

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

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_orders_2 @ X23 @ X22 )
        = ( a_2_0_orders_2 @ X23 @ X22 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

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

thf('43',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('44',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','38','39','40','41','42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('50',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('52',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( X28
        = ( sk_D @ X26 @ X25 @ X28 ) )
      | ~ ( r2_hidden @ X28 @ ( a_2_0_orders_2 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ( X1
        = ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ( X1
        = ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf('65',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','66'])).

thf('68',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('71',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('72',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('73',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ( r2_orders_2 @ X25 @ X27 @ ( sk_D @ X26 @ X25 @ X28 ) )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( a_2_0_orders_2 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('74',plain,(
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
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
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
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
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
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('78',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('79',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('80',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('81',plain,
    ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('87',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82','83','84','85','86','87'])).

thf('89',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','90'])).

thf('92',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('93',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('94',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('95',plain,(
    ! [X25: $i,X26: $i,X28: $i,X29: $i] :
      ( ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r2_hidden @ X28 @ ( a_2_0_orders_2 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X25 ) )
      | ( X28 != X29 )
      | ( r2_hidden @ ( sk_E @ X29 @ X26 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('96',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( r2_hidden @ ( sk_E @ X29 @ X26 @ X25 ) @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X25 ) )
      | ( r2_hidden @ X29 @ ( a_2_0_orders_2 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v2_struct_0 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','97'])).

thf('99',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('101',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('103',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

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

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','103','104','105','106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('112',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('113',plain,
    ( ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('114',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('115',plain,(
    r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['91','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('120',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(t30_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r1_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('121',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r2_orders_2 @ X37 @ X38 @ X36 )
      | ~ ( r1_orders_2 @ X37 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( l1_orders_2 @ X37 )
      | ~ ( v5_orders_2 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t30_orders_2])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_orders_2 @ sk_A @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','126'])).

thf('128',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( r1_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['118','127'])).

thf('129',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('130',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('131',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('132',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('133',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r3_orders_2 @ X33 @ X34 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 )
      | ~ ( v3_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('136',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    r3_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['130','141'])).

thf('143',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('144',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('145',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r1_orders_2 @ X31 @ X30 @ X32 )
      | ~ ( r3_orders_2 @ X31 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('148',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r3_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','150'])).

thf('152',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('154',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    r1_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    $false ),
    inference(demod,[status(thm)],['128','129','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TjlcRkIjQC
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.49/5.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.49/5.70  % Solved by: fo/fo7.sh
% 5.49/5.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.49/5.70  % done 8208 iterations in 5.239s
% 5.49/5.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.49/5.70  % SZS output start Refutation
% 5.49/5.70  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 5.49/5.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.49/5.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.49/5.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.49/5.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.49/5.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.49/5.70  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 5.49/5.70  thf(sk_A_type, type, sk_A: $i).
% 5.49/5.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.49/5.70  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 5.49/5.70  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 5.49/5.70  thf(sk_B_type, type, sk_B: $i > $i).
% 5.49/5.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.49/5.70  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 5.49/5.70  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 5.49/5.70  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 5.49/5.70  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 5.49/5.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.49/5.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.49/5.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.49/5.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.49/5.70  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 5.49/5.70  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 5.49/5.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.49/5.70  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 5.49/5.70  thf(t9_mcart_1, axiom,
% 5.49/5.70    (![A:$i]:
% 5.49/5.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.49/5.70          ( ![B:$i]:
% 5.49/5.70            ( ~( ( r2_hidden @ B @ A ) & 
% 5.49/5.70                 ( ![C:$i,D:$i]:
% 5.49/5.70                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 5.49/5.70                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 5.49/5.70  thf('0', plain,
% 5.49/5.70      (![X16 : $i]:
% 5.49/5.70         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 5.49/5.70      inference('cnf', [status(esa)], [t9_mcart_1])).
% 5.49/5.70  thf(t44_orders_2, conjecture,
% 5.49/5.70    (![A:$i]:
% 5.49/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.49/5.70         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.49/5.70       ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 5.49/5.70  thf(zf_stmt_0, negated_conjecture,
% 5.49/5.70    (~( ![A:$i]:
% 5.49/5.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.49/5.70            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.49/5.70          ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 5.49/5.70    inference('cnf.neg', [status(esa)], [t44_orders_2])).
% 5.49/5.70  thf('1', plain, ((l1_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf(dt_l1_orders_2, axiom,
% 5.49/5.70    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 5.49/5.70  thf('2', plain, (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_orders_2 @ X24))),
% 5.49/5.70      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 5.49/5.70  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 5.49/5.70      inference('sup-', [status(thm)], ['1', '2'])).
% 5.49/5.70  thf(d2_struct_0, axiom,
% 5.49/5.70    (![A:$i]:
% 5.49/5.70     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 5.49/5.70  thf('4', plain,
% 5.49/5.70      (![X19 : $i]:
% 5.49/5.70         (((k1_struct_0 @ X19) = (k1_xboole_0)) | ~ (l1_struct_0 @ X19))),
% 5.49/5.70      inference('cnf', [status(esa)], [d2_struct_0])).
% 5.49/5.70  thf('5', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 5.49/5.70      inference('sup-', [status(thm)], ['3', '4'])).
% 5.49/5.70  thf(t43_orders_2, axiom,
% 5.49/5.70    (![A:$i]:
% 5.49/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.49/5.70         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.49/5.70       ( ( k1_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ))).
% 5.49/5.70  thf('6', plain,
% 5.49/5.70      (![X39 : $i]:
% 5.49/5.70         (((k1_orders_2 @ X39 @ (k1_struct_0 @ X39)) = (u1_struct_0 @ X39))
% 5.49/5.70          | ~ (l1_orders_2 @ X39)
% 5.49/5.70          | ~ (v5_orders_2 @ X39)
% 5.49/5.70          | ~ (v4_orders_2 @ X39)
% 5.49/5.70          | ~ (v3_orders_2 @ X39)
% 5.49/5.70          | (v2_struct_0 @ X39))),
% 5.49/5.70      inference('cnf', [status(esa)], [t43_orders_2])).
% 5.49/5.70  thf('7', plain,
% 5.49/5.70      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 5.49/5.70        | (v2_struct_0 @ sk_A)
% 5.49/5.70        | ~ (v3_orders_2 @ sk_A)
% 5.49/5.70        | ~ (v4_orders_2 @ sk_A)
% 5.49/5.70        | ~ (v5_orders_2 @ sk_A)
% 5.49/5.70        | ~ (l1_orders_2 @ sk_A))),
% 5.49/5.70      inference('sup+', [status(thm)], ['5', '6'])).
% 5.49/5.70  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('9', plain, ((v4_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('10', plain, ((v5_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('12', plain,
% 5.49/5.70      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 5.49/5.70        | (v2_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 5.49/5.70  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('14', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('clc', [status(thm)], ['12', '13'])).
% 5.49/5.70  thf(d3_struct_0, axiom,
% 5.49/5.70    (![A:$i]:
% 5.49/5.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.49/5.70  thf('15', plain,
% 5.49/5.70      (![X20 : $i]:
% 5.49/5.70         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 5.49/5.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.49/5.70  thf('16', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('clc', [status(thm)], ['12', '13'])).
% 5.49/5.70  thf('17', plain,
% 5.49/5.70      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))
% 5.49/5.70        | ~ (l1_struct_0 @ sk_A))),
% 5.49/5.70      inference('sup+', [status(thm)], ['15', '16'])).
% 5.49/5.70  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 5.49/5.70      inference('sup-', [status(thm)], ['1', '2'])).
% 5.49/5.70  thf('19', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['17', '18'])).
% 5.49/5.70  thf('20', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf(dt_k2_subset_1, axiom,
% 5.49/5.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.49/5.70  thf('21', plain,
% 5.49/5.70      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 5.49/5.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.49/5.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.49/5.70  thf('22', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 5.49/5.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.49/5.70  thf('23', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 5.49/5.70      inference('demod', [status(thm)], ['21', '22'])).
% 5.49/5.70  thf(fraenkel_a_2_0_orders_2, axiom,
% 5.49/5.70    (![A:$i,B:$i,C:$i]:
% 5.49/5.70     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 5.49/5.70         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 5.49/5.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 5.49/5.70       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 5.49/5.70         ( ?[D:$i]:
% 5.49/5.70           ( ( ![E:$i]:
% 5.49/5.70               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 5.49/5.70                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 5.49/5.70             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 5.49/5.70  thf('24', plain,
% 5.49/5.70      (![X25 : $i, X26 : $i, X28 : $i]:
% 5.49/5.70         (~ (l1_orders_2 @ X25)
% 5.49/5.70          | ~ (v5_orders_2 @ X25)
% 5.49/5.70          | ~ (v4_orders_2 @ X25)
% 5.49/5.70          | ~ (v3_orders_2 @ X25)
% 5.49/5.70          | (v2_struct_0 @ X25)
% 5.49/5.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 5.49/5.70          | (m1_subset_1 @ (sk_D @ X26 @ X25 @ X28) @ (u1_struct_0 @ X25))
% 5.49/5.70          | ~ (r2_hidden @ X28 @ (a_2_0_orders_2 @ X25 @ X26)))),
% 5.49/5.70      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.49/5.70  thf('25', plain,
% 5.49/5.70      (![X0 : $i, X1 : $i]:
% 5.49/5.70         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.49/5.70          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 5.49/5.70             (u1_struct_0 @ X0))
% 5.49/5.70          | (v2_struct_0 @ X0)
% 5.49/5.70          | ~ (v3_orders_2 @ X0)
% 5.49/5.70          | ~ (v4_orders_2 @ X0)
% 5.49/5.70          | ~ (v5_orders_2 @ X0)
% 5.49/5.70          | ~ (l1_orders_2 @ X0))),
% 5.49/5.70      inference('sup-', [status(thm)], ['23', '24'])).
% 5.49/5.70  thf('26', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.49/5.70          | ~ (l1_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v5_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v4_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v3_orders_2 @ sk_A)
% 5.49/5.70          | (v2_struct_0 @ sk_A)
% 5.49/5.70          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 5.49/5.70             (u1_struct_0 @ sk_A)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['20', '25'])).
% 5.49/5.70  thf('27', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 5.49/5.70      inference('demod', [status(thm)], ['21', '22'])).
% 5.49/5.70  thf('28', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf(d12_orders_2, axiom,
% 5.49/5.70    (![A:$i]:
% 5.49/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.49/5.70         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.49/5.70       ( ![B:$i]:
% 5.49/5.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.49/5.70           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 5.49/5.70  thf('29', plain,
% 5.49/5.70      (![X22 : $i, X23 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 5.49/5.70          | ((k1_orders_2 @ X23 @ X22) = (a_2_0_orders_2 @ X23 @ X22))
% 5.49/5.70          | ~ (l1_orders_2 @ X23)
% 5.49/5.70          | ~ (v5_orders_2 @ X23)
% 5.49/5.70          | ~ (v4_orders_2 @ X23)
% 5.49/5.70          | ~ (v3_orders_2 @ X23)
% 5.49/5.70          | (v2_struct_0 @ X23))),
% 5.49/5.70      inference('cnf', [status(esa)], [d12_orders_2])).
% 5.49/5.70  thf('30', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.49/5.70          | (v2_struct_0 @ sk_A)
% 5.49/5.70          | ~ (v3_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v4_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v5_orders_2 @ sk_A)
% 5.49/5.70          | ~ (l1_orders_2 @ sk_A)
% 5.49/5.70          | ((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['28', '29'])).
% 5.49/5.70  thf('31', plain, ((v3_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('32', plain, ((v4_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('33', plain, ((v5_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('35', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.49/5.70          | (v2_struct_0 @ sk_A)
% 5.49/5.70          | ((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0)))),
% 5.49/5.70      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 5.49/5.70  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('37', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0))
% 5.49/5.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 5.49/5.70      inference('clc', [status(thm)], ['35', '36'])).
% 5.49/5.70  thf('38', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 5.49/5.70         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['27', '37'])).
% 5.49/5.70  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('43', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf('44', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf('45', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.49/5.70          | (v2_struct_0 @ sk_A)
% 5.49/5.70          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 5.49/5.70             (k2_struct_0 @ sk_A)))),
% 5.49/5.70      inference('demod', [status(thm)],
% 5.49/5.70                ['26', '38', '39', '40', '41', '42', '43', '44'])).
% 5.49/5.70  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('47', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 5.49/5.70           (k2_struct_0 @ sk_A))
% 5.49/5.70          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.49/5.70      inference('clc', [status(thm)], ['45', '46'])).
% 5.49/5.70  thf('48', plain,
% 5.49/5.70      ((((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 5.49/5.70        | (m1_subset_1 @ 
% 5.49/5.70           (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.49/5.70            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 5.49/5.70           (k2_struct_0 @ sk_A)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['0', '47'])).
% 5.49/5.70  thf('49', plain,
% 5.49/5.70      (![X16 : $i]:
% 5.49/5.70         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 5.49/5.70      inference('cnf', [status(esa)], [t9_mcart_1])).
% 5.49/5.70  thf('50', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 5.49/5.70      inference('demod', [status(thm)], ['21', '22'])).
% 5.49/5.70  thf('51', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf('52', plain,
% 5.49/5.70      (![X25 : $i, X26 : $i, X28 : $i]:
% 5.49/5.70         (~ (l1_orders_2 @ X25)
% 5.49/5.70          | ~ (v5_orders_2 @ X25)
% 5.49/5.70          | ~ (v4_orders_2 @ X25)
% 5.49/5.70          | ~ (v3_orders_2 @ X25)
% 5.49/5.70          | (v2_struct_0 @ X25)
% 5.49/5.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 5.49/5.70          | ((X28) = (sk_D @ X26 @ X25 @ X28))
% 5.49/5.70          | ~ (r2_hidden @ X28 @ (a_2_0_orders_2 @ X25 @ X26)))),
% 5.49/5.70      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.49/5.70  thf('53', plain,
% 5.49/5.70      (![X0 : $i, X1 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.49/5.70          | ~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ sk_A @ X0))
% 5.49/5.70          | ((X1) = (sk_D @ X0 @ sk_A @ X1))
% 5.49/5.70          | (v2_struct_0 @ sk_A)
% 5.49/5.70          | ~ (v3_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v4_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v5_orders_2 @ sk_A)
% 5.49/5.70          | ~ (l1_orders_2 @ sk_A))),
% 5.49/5.70      inference('sup-', [status(thm)], ['51', '52'])).
% 5.49/5.70  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('55', plain, ((v4_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('56', plain, ((v5_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('58', plain,
% 5.49/5.70      (![X0 : $i, X1 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.49/5.70          | ~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ sk_A @ X0))
% 5.49/5.70          | ((X1) = (sk_D @ X0 @ sk_A @ X1))
% 5.49/5.70          | (v2_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 5.49/5.70  thf('59', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         ((v2_struct_0 @ sk_A)
% 5.49/5.70          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 5.49/5.70          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.49/5.70      inference('sup-', [status(thm)], ['50', '58'])).
% 5.49/5.70  thf('60', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 5.49/5.70         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['27', '37'])).
% 5.49/5.70  thf('61', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         ((v2_struct_0 @ sk_A)
% 5.49/5.70          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 5.49/5.70          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.49/5.70      inference('demod', [status(thm)], ['59', '60'])).
% 5.49/5.70  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('63', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.49/5.70          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0)))),
% 5.49/5.70      inference('clc', [status(thm)], ['61', '62'])).
% 5.49/5.70  thf('64', plain,
% 5.49/5.70      ((((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 5.49/5.70        | ((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.49/5.70            = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.49/5.70               (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))))),
% 5.49/5.70      inference('sup-', [status(thm)], ['49', '63'])).
% 5.49/5.70  thf('65', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('66', plain,
% 5.49/5.70      (((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.49/5.70         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.49/5.70            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.49/5.70      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 5.49/5.70  thf('67', plain,
% 5.49/5.70      ((((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 5.49/5.70        | (m1_subset_1 @ 
% 5.49/5.70           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.49/5.70           (k2_struct_0 @ sk_A)))),
% 5.49/5.70      inference('demod', [status(thm)], ['48', '66'])).
% 5.49/5.70  thf('68', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('69', plain,
% 5.49/5.70      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.49/5.70        (k2_struct_0 @ sk_A))),
% 5.49/5.70      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.49/5.70  thf('70', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf('71', plain,
% 5.49/5.70      (![X16 : $i]:
% 5.49/5.70         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 5.49/5.70      inference('cnf', [status(esa)], [t9_mcart_1])).
% 5.49/5.70  thf('72', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 5.49/5.70      inference('demod', [status(thm)], ['21', '22'])).
% 5.49/5.70  thf('73', plain,
% 5.49/5.70      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.49/5.70         (~ (l1_orders_2 @ X25)
% 5.49/5.70          | ~ (v5_orders_2 @ X25)
% 5.49/5.70          | ~ (v4_orders_2 @ X25)
% 5.49/5.70          | ~ (v3_orders_2 @ X25)
% 5.49/5.70          | (v2_struct_0 @ X25)
% 5.49/5.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 5.49/5.70          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 5.49/5.70          | (r2_orders_2 @ X25 @ X27 @ (sk_D @ X26 @ X25 @ X28))
% 5.49/5.70          | ~ (r2_hidden @ X27 @ X26)
% 5.49/5.70          | ~ (r2_hidden @ X28 @ (a_2_0_orders_2 @ X25 @ X26)))),
% 5.49/5.70      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.49/5.70  thf('74', plain,
% 5.49/5.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.49/5.70         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.49/5.70          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 5.49/5.70          | (r2_orders_2 @ X0 @ X2 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.49/5.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 5.49/5.70          | (v2_struct_0 @ X0)
% 5.49/5.70          | ~ (v3_orders_2 @ X0)
% 5.49/5.70          | ~ (v4_orders_2 @ X0)
% 5.49/5.70          | ~ (v5_orders_2 @ X0)
% 5.49/5.70          | ~ (l1_orders_2 @ X0))),
% 5.49/5.70      inference('sup-', [status(thm)], ['72', '73'])).
% 5.49/5.70  thf('75', plain,
% 5.49/5.70      (![X0 : $i, X1 : $i]:
% 5.49/5.70         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 5.49/5.70          | ~ (l1_orders_2 @ X0)
% 5.49/5.70          | ~ (v5_orders_2 @ X0)
% 5.49/5.70          | ~ (v4_orders_2 @ X0)
% 5.49/5.70          | ~ (v3_orders_2 @ X0)
% 5.49/5.70          | (v2_struct_0 @ X0)
% 5.49/5.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.49/5.70          | (r2_orders_2 @ X0 @ X1 @ 
% 5.49/5.70             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.49/5.70              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 5.49/5.70          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['71', '74'])).
% 5.49/5.70  thf('76', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.49/5.70          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.49/5.70          | (r2_orders_2 @ sk_A @ X0 @ 
% 5.49/5.70             (sk_D @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 5.49/5.70              (sk_B @ (a_2_0_orders_2 @ sk_A @ (u1_struct_0 @ sk_A)))))
% 5.49/5.70          | (v2_struct_0 @ sk_A)
% 5.49/5.70          | ~ (v3_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v4_orders_2 @ sk_A)
% 5.49/5.70          | ~ (v5_orders_2 @ sk_A)
% 5.49/5.70          | ~ (l1_orders_2 @ sk_A)
% 5.49/5.70          | ((a_2_0_orders_2 @ sk_A @ (u1_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['70', '75'])).
% 5.49/5.70  thf('77', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf('78', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf('79', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf('80', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 5.49/5.70         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['27', '37'])).
% 5.49/5.70  thf('81', plain,
% 5.49/5.70      (((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 5.49/5.70         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 5.49/5.70            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.49/5.70      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 5.49/5.70  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('86', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf('87', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 5.49/5.70         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['27', '37'])).
% 5.49/5.70  thf('88', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.49/5.70          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 5.49/5.70          | (r2_orders_2 @ sk_A @ X0 @ 
% 5.49/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.49/5.70          | (v2_struct_0 @ sk_A)
% 5.49/5.70          | ((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 5.49/5.70      inference('demod', [status(thm)],
% 5.49/5.70                ['76', '77', '78', '79', '80', '81', '82', '83', '84', '85', 
% 5.49/5.70                 '86', '87'])).
% 5.49/5.70  thf('89', plain,
% 5.49/5.70      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 5.49/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.70  thf('90', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.49/5.70          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 5.49/5.70          | (r2_orders_2 @ sk_A @ X0 @ 
% 5.49/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.49/5.70          | (v2_struct_0 @ sk_A))),
% 5.49/5.70      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 5.49/5.70  thf('91', plain,
% 5.49/5.70      (((v2_struct_0 @ sk_A)
% 5.49/5.70        | (r2_orders_2 @ sk_A @ 
% 5.49/5.70           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.49/5.70           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.49/5.70        | ~ (r2_hidden @ 
% 5.49/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.49/5.70             (k2_struct_0 @ sk_A)))),
% 5.49/5.70      inference('sup-', [status(thm)], ['69', '90'])).
% 5.49/5.70  thf('92', plain,
% 5.49/5.70      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.49/5.70        (k2_struct_0 @ sk_A))),
% 5.49/5.70      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.49/5.70  thf('93', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.49/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.49/5.70  thf(t4_subset_1, axiom,
% 5.49/5.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.49/5.70  thf('94', plain,
% 5.49/5.70      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.49/5.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.49/5.70  thf('95', plain,
% 5.49/5.70      (![X25 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 5.49/5.70         (~ (l1_orders_2 @ X25)
% 5.49/5.70          | ~ (v5_orders_2 @ X25)
% 5.49/5.70          | ~ (v4_orders_2 @ X25)
% 5.49/5.70          | ~ (v3_orders_2 @ X25)
% 5.49/5.70          | (v2_struct_0 @ X25)
% 5.49/5.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 5.49/5.70          | (r2_hidden @ X28 @ (a_2_0_orders_2 @ X25 @ X26))
% 5.49/5.70          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X25))
% 5.49/5.70          | ((X28) != (X29))
% 5.49/5.70          | (r2_hidden @ (sk_E @ X29 @ X26 @ X25) @ X26))),
% 5.49/5.70      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.49/5.70  thf('96', plain,
% 5.49/5.70      (![X25 : $i, X26 : $i, X29 : $i]:
% 5.49/5.70         ((r2_hidden @ (sk_E @ X29 @ X26 @ X25) @ X26)
% 5.49/5.70          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X25))
% 5.49/5.70          | (r2_hidden @ X29 @ (a_2_0_orders_2 @ X25 @ X26))
% 5.49/5.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 5.49/5.70          | (v2_struct_0 @ X25)
% 5.49/5.70          | ~ (v3_orders_2 @ X25)
% 5.49/5.70          | ~ (v4_orders_2 @ X25)
% 5.49/5.70          | ~ (v5_orders_2 @ X25)
% 5.49/5.70          | ~ (l1_orders_2 @ X25))),
% 5.49/5.70      inference('simplify', [status(thm)], ['95'])).
% 5.49/5.70  thf('97', plain,
% 5.49/5.70      (![X0 : $i, X1 : $i]:
% 5.49/5.70         (~ (l1_orders_2 @ X0)
% 5.49/5.70          | ~ (v5_orders_2 @ X0)
% 5.49/5.70          | ~ (v4_orders_2 @ X0)
% 5.49/5.70          | ~ (v3_orders_2 @ X0)
% 5.49/5.70          | (v2_struct_0 @ X0)
% 5.49/5.70          | (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ k1_xboole_0))
% 5.49/5.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.49/5.70          | (r2_hidden @ (sk_E @ X1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 5.49/5.70      inference('sup-', [status(thm)], ['94', '96'])).
% 5.49/5.70  thf('98', plain,
% 5.49/5.70      (![X0 : $i]:
% 5.49/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.49/5.70          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 5.49/5.70          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ k1_xboole_0))
% 5.54/5.70          | (v2_struct_0 @ sk_A)
% 5.54/5.70          | ~ (v3_orders_2 @ sk_A)
% 5.54/5.70          | ~ (v4_orders_2 @ sk_A)
% 5.54/5.70          | ~ (v5_orders_2 @ sk_A)
% 5.54/5.70          | ~ (l1_orders_2 @ sk_A))),
% 5.54/5.70      inference('sup-', [status(thm)], ['93', '97'])).
% 5.54/5.70  thf('99', plain,
% 5.54/5.70      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.54/5.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.54/5.70  thf('100', plain,
% 5.54/5.70      (![X0 : $i]:
% 5.54/5.70         (((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0))
% 5.54/5.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 5.54/5.70      inference('clc', [status(thm)], ['35', '36'])).
% 5.54/5.70  thf('101', plain,
% 5.54/5.70      (((k1_orders_2 @ sk_A @ k1_xboole_0)
% 5.54/5.70         = (a_2_0_orders_2 @ sk_A @ k1_xboole_0))),
% 5.54/5.70      inference('sup-', [status(thm)], ['99', '100'])).
% 5.54/5.70  thf('102', plain,
% 5.54/5.70      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['17', '18'])).
% 5.54/5.70  thf('103', plain,
% 5.54/5.70      (((k2_struct_0 @ sk_A) = (a_2_0_orders_2 @ sk_A @ k1_xboole_0))),
% 5.54/5.70      inference('demod', [status(thm)], ['101', '102'])).
% 5.54/5.70  thf('104', plain, ((v3_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('105', plain, ((v4_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('106', plain, ((v5_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('108', plain,
% 5.54/5.70      (![X0 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 5.54/5.70          | (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | (v2_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)],
% 5.54/5.70                ['98', '103', '104', '105', '106', '107'])).
% 5.54/5.70  thf('109', plain,
% 5.54/5.70      (((v2_struct_0 @ sk_A)
% 5.54/5.70        | (r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70           (k2_struct_0 @ sk_A))
% 5.54/5.70        | (r2_hidden @ 
% 5.54/5.70           (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70            k1_xboole_0 @ sk_A) @ 
% 5.54/5.70           k1_xboole_0))),
% 5.54/5.70      inference('sup-', [status(thm)], ['92', '108'])).
% 5.54/5.70  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('111', plain,
% 5.54/5.70      (((r2_hidden @ 
% 5.54/5.70         (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70          k1_xboole_0 @ sk_A) @ 
% 5.54/5.70         k1_xboole_0)
% 5.54/5.70        | (r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70           (k2_struct_0 @ sk_A)))),
% 5.54/5.70      inference('clc', [status(thm)], ['109', '110'])).
% 5.54/5.70  thf(t7_ordinal1, axiom,
% 5.54/5.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.54/5.70  thf('112', plain,
% 5.54/5.70      (![X14 : $i, X15 : $i]:
% 5.54/5.70         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 5.54/5.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.54/5.70  thf('113', plain,
% 5.54/5.70      (((r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70         (k2_struct_0 @ sk_A))
% 5.54/5.70        | ~ (r1_tarski @ k1_xboole_0 @ 
% 5.54/5.70             (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70              k1_xboole_0 @ sk_A)))),
% 5.54/5.70      inference('sup-', [status(thm)], ['111', '112'])).
% 5.54/5.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.54/5.70  thf('114', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 5.54/5.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.54/5.70  thf('115', plain,
% 5.54/5.70      ((r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (k2_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['113', '114'])).
% 5.54/5.70  thf('116', plain,
% 5.54/5.70      (((v2_struct_0 @ sk_A)
% 5.54/5.70        | (r2_orders_2 @ sk_A @ 
% 5.54/5.70           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.54/5.70      inference('demod', [status(thm)], ['91', '115'])).
% 5.54/5.70  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('118', plain,
% 5.54/5.70      ((r2_orders_2 @ sk_A @ 
% 5.54/5.70        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.54/5.70      inference('clc', [status(thm)], ['116', '117'])).
% 5.54/5.70  thf('119', plain,
% 5.54/5.70      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (k2_struct_0 @ sk_A))),
% 5.54/5.70      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.54/5.70  thf('120', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.54/5.70  thf(t30_orders_2, axiom,
% 5.54/5.70    (![A:$i]:
% 5.54/5.70     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.54/5.70       ( ![B:$i]:
% 5.54/5.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.54/5.70           ( ![C:$i]:
% 5.54/5.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.54/5.70               ( ~( ( r1_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 5.54/5.70  thf('121', plain,
% 5.54/5.70      (![X36 : $i, X37 : $i, X38 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 5.54/5.70          | ~ (r2_orders_2 @ X37 @ X38 @ X36)
% 5.54/5.70          | ~ (r1_orders_2 @ X37 @ X36 @ X38)
% 5.54/5.70          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 5.54/5.70          | ~ (l1_orders_2 @ X37)
% 5.54/5.70          | ~ (v5_orders_2 @ X37))),
% 5.54/5.70      inference('cnf', [status(esa)], [t30_orders_2])).
% 5.54/5.70  thf('122', plain,
% 5.54/5.70      (![X0 : $i, X1 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | ~ (v5_orders_2 @ sk_A)
% 5.54/5.70          | ~ (l1_orders_2 @ sk_A)
% 5.54/5.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.54/5.70          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.54/5.70          | ~ (r2_orders_2 @ sk_A @ X1 @ X0))),
% 5.54/5.70      inference('sup-', [status(thm)], ['120', '121'])).
% 5.54/5.70  thf('123', plain, ((v5_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('124', plain, ((l1_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('125', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.54/5.70  thf('126', plain,
% 5.54/5.70      (![X0 : $i, X1 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | ~ (m1_subset_1 @ X1 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.54/5.70          | ~ (r2_orders_2 @ sk_A @ X1 @ X0))),
% 5.54/5.70      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 5.54/5.70  thf('127', plain,
% 5.54/5.70      (![X0 : $i]:
% 5.54/5.70         (~ (r2_orders_2 @ sk_A @ X0 @ 
% 5.54/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.54/5.70          | ~ (r1_orders_2 @ sk_A @ 
% 5.54/5.70               (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ X0)
% 5.54/5.70          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A)))),
% 5.54/5.70      inference('sup-', [status(thm)], ['119', '126'])).
% 5.54/5.70  thf('128', plain,
% 5.54/5.70      ((~ (m1_subset_1 @ 
% 5.54/5.70           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70           (k2_struct_0 @ sk_A))
% 5.54/5.70        | ~ (r1_orders_2 @ sk_A @ 
% 5.54/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.54/5.70      inference('sup-', [status(thm)], ['118', '127'])).
% 5.54/5.70  thf('129', plain,
% 5.54/5.70      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (k2_struct_0 @ sk_A))),
% 5.54/5.70      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.54/5.70  thf('130', plain,
% 5.54/5.70      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (k2_struct_0 @ sk_A))),
% 5.54/5.70      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.54/5.70  thf('131', plain,
% 5.54/5.70      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (k2_struct_0 @ sk_A))),
% 5.54/5.70      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.54/5.70  thf('132', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.54/5.70  thf(reflexivity_r3_orders_2, axiom,
% 5.54/5.70    (![A:$i,B:$i,C:$i]:
% 5.54/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.54/5.70         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 5.54/5.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 5.54/5.70       ( r3_orders_2 @ A @ B @ B ) ))).
% 5.54/5.70  thf('133', plain,
% 5.54/5.70      (![X33 : $i, X34 : $i, X35 : $i]:
% 5.54/5.70         ((r3_orders_2 @ X33 @ X34 @ X34)
% 5.54/5.70          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 5.54/5.70          | ~ (l1_orders_2 @ X33)
% 5.54/5.70          | ~ (v3_orders_2 @ X33)
% 5.54/5.70          | (v2_struct_0 @ X33)
% 5.54/5.70          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X33)))),
% 5.54/5.70      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 5.54/5.70  thf('134', plain,
% 5.54/5.70      (![X0 : $i, X1 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.54/5.70          | (v2_struct_0 @ sk_A)
% 5.54/5.70          | ~ (v3_orders_2 @ sk_A)
% 5.54/5.70          | ~ (l1_orders_2 @ sk_A)
% 5.54/5.70          | (r3_orders_2 @ sk_A @ X0 @ X0))),
% 5.54/5.70      inference('sup-', [status(thm)], ['132', '133'])).
% 5.54/5.70  thf('135', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.54/5.70  thf('136', plain, ((v3_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('137', plain, ((l1_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('138', plain,
% 5.54/5.70      (![X0 : $i, X1 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | ~ (m1_subset_1 @ X1 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | (v2_struct_0 @ sk_A)
% 5.54/5.70          | (r3_orders_2 @ sk_A @ X0 @ X0))),
% 5.54/5.70      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 5.54/5.70  thf('139', plain,
% 5.54/5.70      (![X0 : $i]:
% 5.54/5.70         ((r3_orders_2 @ sk_A @ 
% 5.54/5.70           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.54/5.70          | (v2_struct_0 @ sk_A)
% 5.54/5.70          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A)))),
% 5.54/5.70      inference('sup-', [status(thm)], ['131', '138'])).
% 5.54/5.70  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('141', plain,
% 5.54/5.70      (![X0 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | (r3_orders_2 @ sk_A @ 
% 5.54/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 5.54/5.70      inference('clc', [status(thm)], ['139', '140'])).
% 5.54/5.70  thf('142', plain,
% 5.54/5.70      ((r3_orders_2 @ sk_A @ 
% 5.54/5.70        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.54/5.70      inference('sup-', [status(thm)], ['130', '141'])).
% 5.54/5.70  thf('143', plain,
% 5.54/5.70      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (k2_struct_0 @ sk_A))),
% 5.54/5.70      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.54/5.70  thf('144', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.54/5.70  thf(redefinition_r3_orders_2, axiom,
% 5.54/5.70    (![A:$i,B:$i,C:$i]:
% 5.54/5.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.54/5.70         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 5.54/5.70         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 5.54/5.70       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 5.54/5.70  thf('145', plain,
% 5.54/5.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 5.54/5.70          | ~ (l1_orders_2 @ X31)
% 5.54/5.70          | ~ (v3_orders_2 @ X31)
% 5.54/5.70          | (v2_struct_0 @ X31)
% 5.54/5.70          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 5.54/5.70          | (r1_orders_2 @ X31 @ X30 @ X32)
% 5.54/5.70          | ~ (r3_orders_2 @ X31 @ X30 @ X32))),
% 5.54/5.70      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 5.54/5.70  thf('146', plain,
% 5.54/5.70      (![X0 : $i, X1 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | ~ (r3_orders_2 @ sk_A @ X0 @ X1)
% 5.54/5.70          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.54/5.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 5.54/5.70          | (v2_struct_0 @ sk_A)
% 5.54/5.70          | ~ (v3_orders_2 @ sk_A)
% 5.54/5.70          | ~ (l1_orders_2 @ sk_A))),
% 5.54/5.70      inference('sup-', [status(thm)], ['144', '145'])).
% 5.54/5.70  thf('147', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['14', '19'])).
% 5.54/5.70  thf('148', plain, ((v3_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('149', plain, ((l1_orders_2 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('150', plain,
% 5.54/5.70      (![X0 : $i, X1 : $i]:
% 5.54/5.70         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | ~ (r3_orders_2 @ sk_A @ X0 @ X1)
% 5.54/5.70          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 5.54/5.70          | ~ (m1_subset_1 @ X1 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | (v2_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 5.54/5.70  thf('151', plain,
% 5.54/5.70      (![X0 : $i]:
% 5.54/5.70         ((v2_struct_0 @ sk_A)
% 5.54/5.70          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 5.54/5.70          | (r1_orders_2 @ sk_A @ 
% 5.54/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ X0)
% 5.54/5.70          | ~ (r3_orders_2 @ sk_A @ 
% 5.54/5.70               (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ X0))),
% 5.54/5.70      inference('sup-', [status(thm)], ['143', '150'])).
% 5.54/5.70  thf('152', plain,
% 5.54/5.70      (((r1_orders_2 @ sk_A @ 
% 5.54/5.70         (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70         (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.54/5.70        | ~ (m1_subset_1 @ 
% 5.54/5.70             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70             (k2_struct_0 @ sk_A))
% 5.54/5.70        | (v2_struct_0 @ sk_A))),
% 5.54/5.70      inference('sup-', [status(thm)], ['142', '151'])).
% 5.54/5.70  thf('153', plain,
% 5.54/5.70      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (k2_struct_0 @ sk_A))),
% 5.54/5.70      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.54/5.70  thf('154', plain,
% 5.54/5.70      (((r1_orders_2 @ sk_A @ 
% 5.54/5.70         (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70         (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 5.54/5.70        | (v2_struct_0 @ sk_A))),
% 5.54/5.70      inference('demod', [status(thm)], ['152', '153'])).
% 5.54/5.70  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 5.54/5.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.54/5.70  thf('156', plain,
% 5.54/5.70      ((r1_orders_2 @ sk_A @ 
% 5.54/5.70        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 5.54/5.70        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 5.54/5.70      inference('clc', [status(thm)], ['154', '155'])).
% 5.54/5.70  thf('157', plain, ($false),
% 5.54/5.70      inference('demod', [status(thm)], ['128', '129', '156'])).
% 5.54/5.70  
% 5.54/5.70  % SZS output end Refutation
% 5.54/5.70  
% 5.54/5.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
