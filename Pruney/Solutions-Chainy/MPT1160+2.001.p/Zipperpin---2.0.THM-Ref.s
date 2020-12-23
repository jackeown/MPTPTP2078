%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sxGOXUd5V8

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:59 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 153 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  601 (1442 expanded)
%              Number of equality atoms :   12 (  52 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t60_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_orders_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X32 @ X31 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X30: $i] :
      ( ( ( k1_struct_0 @ X30 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('24',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('27',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['15','33'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t57_orders_2,axiom,(
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
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( r2_hidden @ X35 @ ( k3_orders_2 @ X36 @ X37 @ X38 ) )
      | ( r2_hidden @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ X1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

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
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['31','32'])).

thf('50',plain,(
    r2_hidden @ ( sk_B @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sxGOXUd5V8
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 399 iterations in 0.326s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.59/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.78  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.59/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.59/0.78  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i > $i).
% 0.59/0.78  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.59/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.78  thf(d1_xboole_0, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.78  thf(t60_orders_2, conjecture,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.78         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i]:
% 0.59/0.78        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.78            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.78          ( ![B:$i]:
% 0.59/0.78            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.59/0.78  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t4_subset_1, axiom,
% 0.59/0.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.59/0.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.78  thf(dt_k3_orders_2, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.78         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.59/0.78         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.78       ( m1_subset_1 @
% 0.59/0.78         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.59/0.78          | ~ (l1_orders_2 @ X32)
% 0.59/0.78          | ~ (v5_orders_2 @ X32)
% 0.59/0.78          | ~ (v4_orders_2 @ X32)
% 0.59/0.78          | ~ (v3_orders_2 @ X32)
% 0.59/0.78          | (v2_struct_0 @ X32)
% 0.59/0.78          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.59/0.78          | (m1_subset_1 @ (k3_orders_2 @ X32 @ X31 @ X33) @ 
% 0.59/0.78             (k1_zfmisc_1 @ (u1_struct_0 @ X32))))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.59/0.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.59/0.78          | (v2_struct_0 @ X0)
% 0.59/0.78          | ~ (v3_orders_2 @ X0)
% 0.59/0.78          | ~ (v4_orders_2 @ X0)
% 0.59/0.78          | ~ (v5_orders_2 @ X0)
% 0.59/0.78          | ~ (l1_orders_2 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      ((~ (l1_orders_2 @ sk_A)
% 0.59/0.78        | ~ (v5_orders_2 @ sk_A)
% 0.59/0.78        | ~ (v4_orders_2 @ sk_A)
% 0.59/0.78        | ~ (v3_orders_2 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '4'])).
% 0.59/0.78  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A)
% 0.59/0.78        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.78      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.59/0.78  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('clc', [status(thm)], ['10', '11'])).
% 0.59/0.78  thf(t4_subset, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.59/0.78       ( m1_subset_1 @ A @ C ) ))).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X16 @ X17)
% 0.59/0.78          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.59/0.78          | (m1_subset_1 @ X16 @ X18))),
% 0.59/0.78      inference('cnf', [status(esa)], [t4_subset])).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (((v1_xboole_0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1))
% 0.59/0.78        | (m1_subset_1 @ 
% 0.59/0.78           (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.59/0.78           (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['0', '14'])).
% 0.59/0.78  thf(d3_tarski, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      (![X4 : $i, X6 : $i]:
% 0.59/0.78         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.59/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf(d10_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X7 : $i, X9 : $i]:
% 0.59/0.78         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['18', '21'])).
% 0.59/0.78  thf(d2_struct_0, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (![X30 : $i]:
% 0.59/0.78         (((k1_struct_0 @ X30) = (k1_xboole_0)) | ~ (l1_struct_0 @ X30))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))
% 0.59/0.78        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.78  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(dt_l1_orders_2, axiom,
% 0.59/0.78    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.78  thf('27', plain,
% 0.59/0.78      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_orders_2 @ X34))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.59/0.78  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['25', '28'])).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((X0) != (k1_xboole_0))
% 0.59/0.78          | ~ (v1_xboole_0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1))
% 0.59/0.78          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['22', '29'])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.78        | ~ (v1_xboole_0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['30'])).
% 0.59/0.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.78  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      (~ (v1_xboole_0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.59/0.78      inference('simplify_reflect+', [status(thm)], ['31', '32'])).
% 0.59/0.78  thf('34', plain,
% 0.59/0.78      ((m1_subset_1 @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.59/0.78        (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('clc', [status(thm)], ['15', '33'])).
% 0.59/0.78  thf('35', plain,
% 0.59/0.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.59/0.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.78  thf(t57_orders_2, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.78         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78           ( ![C:$i]:
% 0.59/0.78             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78               ( ![D:$i]:
% 0.59/0.78                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.78                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.59/0.78                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 0.59/0.78          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.59/0.78          | ~ (r2_hidden @ X35 @ (k3_orders_2 @ X36 @ X37 @ X38))
% 0.59/0.78          | (r2_hidden @ X35 @ X37)
% 0.59/0.78          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 0.59/0.78          | ~ (l1_orders_2 @ X36)
% 0.59/0.78          | ~ (v5_orders_2 @ X36)
% 0.59/0.78          | ~ (v4_orders_2 @ X36)
% 0.59/0.78          | ~ (v3_orders_2 @ X36)
% 0.59/0.78          | (v2_struct_0 @ X36))),
% 0.59/0.78      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.59/0.78  thf('38', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((v2_struct_0 @ X0)
% 0.59/0.78          | ~ (v3_orders_2 @ X0)
% 0.59/0.78          | ~ (v4_orders_2 @ X0)
% 0.59/0.78          | ~ (v5_orders_2 @ X0)
% 0.59/0.78          | ~ (l1_orders_2 @ X0)
% 0.59/0.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.59/0.78          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.59/0.78          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.59/0.78          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.59/0.78               (u1_struct_0 @ X1))
% 0.59/0.78          | (r2_hidden @ (sk_B @ (k3_orders_2 @ X1 @ k1_xboole_0 @ X0)) @ 
% 0.59/0.78             k1_xboole_0)
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.59/0.78          | ~ (l1_orders_2 @ X1)
% 0.59/0.78          | ~ (v5_orders_2 @ X1)
% 0.59/0.78          | ~ (v4_orders_2 @ X1)
% 0.59/0.78          | ~ (v3_orders_2 @ X1)
% 0.59/0.78          | (v2_struct_0 @ X1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['35', '38'])).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A)
% 0.59/0.78        | ~ (v3_orders_2 @ sk_A)
% 0.59/0.78        | ~ (v4_orders_2 @ sk_A)
% 0.59/0.78        | ~ (v5_orders_2 @ sk_A)
% 0.59/0.78        | ~ (l1_orders_2 @ sk_A)
% 0.59/0.78        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.59/0.78           k1_xboole_0)
% 0.59/0.78        | (v1_xboole_0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['34', '39'])).
% 0.59/0.78  thf('41', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('42', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('44', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('45', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('46', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A)
% 0.59/0.78        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.59/0.78           k1_xboole_0)
% 0.59/0.78        | (v1_xboole_0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.59/0.78      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.59/0.78  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('48', plain,
% 0.59/0.78      (((v1_xboole_0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1))
% 0.59/0.78        | (r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.59/0.78           k1_xboole_0))),
% 0.59/0.78      inference('clc', [status(thm)], ['46', '47'])).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      (~ (v1_xboole_0 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.59/0.78      inference('simplify_reflect+', [status(thm)], ['31', '32'])).
% 0.59/0.78  thf('50', plain,
% 0.59/0.78      ((r2_hidden @ (sk_B @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B_1)) @ 
% 0.59/0.78        k1_xboole_0)),
% 0.59/0.78      inference('clc', [status(thm)], ['48', '49'])).
% 0.59/0.78  thf('51', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.78  thf('52', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.78  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.78  thf('54', plain, ($false), inference('demod', [status(thm)], ['52', '53'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
