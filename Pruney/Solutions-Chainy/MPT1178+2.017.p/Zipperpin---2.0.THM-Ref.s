%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lDGuUNYkbr

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:22 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 157 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  611 (1739 expanded)
%              Number of equality atoms :   20 (  70 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t87_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
           != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
             != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_orders_2])).

thf('0',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X18 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X16 ) @ ( k3_tarski @ X17 ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ X0 ) @ ( sk_B @ X0 ) )
      | ( ( k3_tarski @ X0 )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      = ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_xboole_0
      = ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ~ ( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_orders_1 @ X30 @ ( k1_orders_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
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
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( k1_xboole_0
    = ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('30',plain,(
    r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( C
                = ( k4_orders_2 @ A @ B ) )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ C )
                <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ~ ( m1_orders_1 @ X23 @ ( k1_orders_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( X25
       != ( k4_orders_2 @ X24 @ X23 ) )
      | ( m2_orders_2 @ X27 @ X24 @ X23 )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X27: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( r2_hidden @ X27 @ ( k4_orders_2 @ X24 @ X23 ) )
      | ( m2_orders_2 @ X27 @ X24 @ X23 )
      | ~ ( m1_orders_1 @ X23 @ ( k1_orders_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) )).

thf('44',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_orders_1 @ X31 @ ( k1_orders_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X31 @ ( u1_struct_0 @ X32 ) ) @ X33 )
      | ~ ( m2_orders_2 @ X33 @ X32 @ X31 )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','52'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('sup-',[status(thm)],['53','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lDGuUNYkbr
% 0.15/0.37  % Computer   : n025.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 13:07:21 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 78 iterations in 0.026s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.23/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.48  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.23/0.48  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.23/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.48  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.23/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.23/0.48  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.23/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.23/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.48  thf(t87_orders_2, conjecture,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i]:
% 0.23/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.48            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.48          ( ![B:$i]:
% 0.23/0.48            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(d1_xboole_0, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.48  thf(t63_subset_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( r2_hidden @ A @ B ) =>
% 0.23/0.48       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X18 : $i, X19 : $i]:
% 0.23/0.48         ((m1_subset_1 @ (k1_tarski @ X18) @ (k1_zfmisc_1 @ X19))
% 0.23/0.48          | ~ (r2_hidden @ X18 @ X19))),
% 0.23/0.48      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v1_xboole_0 @ X0)
% 0.23/0.48          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.48  thf(t3_subset, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.48  thf('4', plain,
% 0.23/0.48      (![X20 : $i, X21 : $i]:
% 0.23/0.48         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.23/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.48  thf('5', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.48  thf(t95_zfmisc_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.23/0.48       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.23/0.48  thf('6', plain,
% 0.23/0.48      (![X16 : $i, X17 : $i]:
% 0.23/0.48         ((r1_tarski @ (k3_tarski @ X16) @ (k3_tarski @ X17))
% 0.23/0.48          | ~ (r1_tarski @ X16 @ X17))),
% 0.23/0.48      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.23/0.48  thf('7', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v1_xboole_0 @ X0)
% 0.23/0.48          | (r1_tarski @ (k3_tarski @ (k1_tarski @ (sk_B @ X0))) @ 
% 0.23/0.48             (k3_tarski @ X0)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.48  thf(t31_zfmisc_1, axiom,
% 0.23/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.23/0.48  thf('8', plain, (![X15 : $i]: ((k3_tarski @ (k1_tarski @ X15)) = (X15))),
% 0.23/0.48      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.23/0.48  thf('9', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v1_xboole_0 @ X0) | (r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0)))),
% 0.23/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.48  thf(d10_xboole_0, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.48  thf('10', plain,
% 0.23/0.48      (![X3 : $i, X5 : $i]:
% 0.23/0.48         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.23/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.48  thf('11', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v1_xboole_0 @ X0)
% 0.23/0.48          | ~ (r1_tarski @ (k3_tarski @ X0) @ (sk_B @ X0))
% 0.23/0.48          | ((k3_tarski @ X0) = (sk_B @ X0)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.48  thf('12', plain,
% 0.23/0.48      ((~ (r1_tarski @ k1_xboole_0 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.23/0.48        | ((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.23/0.48            = (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.23/0.48        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['0', '11'])).
% 0.23/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.48  thf('13', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.23/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.48  thf('14', plain,
% 0.23/0.48      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('15', plain,
% 0.23/0.48      ((((k1_xboole_0) = (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.23/0.48        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.23/0.48      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.23/0.48  thf('16', plain,
% 0.23/0.48      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(fc9_orders_2, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.23/0.48         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.48       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.23/0.48  thf('17', plain,
% 0.23/0.48      (![X29 : $i, X30 : $i]:
% 0.23/0.48         (~ (l1_orders_2 @ X29)
% 0.23/0.48          | ~ (v5_orders_2 @ X29)
% 0.23/0.48          | ~ (v4_orders_2 @ X29)
% 0.23/0.48          | ~ (v3_orders_2 @ X29)
% 0.23/0.48          | (v2_struct_0 @ X29)
% 0.23/0.48          | ~ (m1_orders_1 @ X30 @ (k1_orders_1 @ (u1_struct_0 @ X29)))
% 0.23/0.48          | ~ (v1_xboole_0 @ (k4_orders_2 @ X29 @ X30)))),
% 0.23/0.48      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.23/0.48  thf('18', plain,
% 0.23/0.48      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.23/0.48        | (v2_struct_0 @ sk_A)
% 0.23/0.48        | ~ (v3_orders_2 @ sk_A)
% 0.23/0.48        | ~ (v4_orders_2 @ sk_A)
% 0.23/0.48        | ~ (v5_orders_2 @ sk_A)
% 0.23/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.48  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('23', plain,
% 0.23/0.48      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.23/0.48      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.23/0.48  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('25', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.23/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.23/0.48  thf('26', plain, (((k1_xboole_0) = (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.23/0.48      inference('clc', [status(thm)], ['15', '25'])).
% 0.23/0.48  thf('27', plain,
% 0.23/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.48  thf('28', plain,
% 0.23/0.48      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.23/0.48        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.23/0.48      inference('sup+', [status(thm)], ['26', '27'])).
% 0.23/0.48  thf('29', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.23/0.48      inference('clc', [status(thm)], ['23', '24'])).
% 0.23/0.48  thf('30', plain, ((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.23/0.48      inference('clc', [status(thm)], ['28', '29'])).
% 0.23/0.48  thf('31', plain,
% 0.23/0.48      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(d17_orders_2, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ![C:$i]:
% 0.23/0.48             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.23/0.48               ( ![D:$i]:
% 0.23/0.48                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.23/0.48  thf('32', plain,
% 0.23/0.48      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.23/0.48         (~ (m1_orders_1 @ X23 @ (k1_orders_1 @ (u1_struct_0 @ X24)))
% 0.23/0.48          | ((X25) != (k4_orders_2 @ X24 @ X23))
% 0.23/0.48          | (m2_orders_2 @ X27 @ X24 @ X23)
% 0.23/0.48          | ~ (r2_hidden @ X27 @ X25)
% 0.23/0.48          | ~ (l1_orders_2 @ X24)
% 0.23/0.48          | ~ (v5_orders_2 @ X24)
% 0.23/0.48          | ~ (v4_orders_2 @ X24)
% 0.23/0.48          | ~ (v3_orders_2 @ X24)
% 0.23/0.48          | (v2_struct_0 @ X24))),
% 0.23/0.48      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.23/0.48  thf('33', plain,
% 0.23/0.48      (![X23 : $i, X24 : $i, X27 : $i]:
% 0.23/0.48         ((v2_struct_0 @ X24)
% 0.23/0.48          | ~ (v3_orders_2 @ X24)
% 0.23/0.48          | ~ (v4_orders_2 @ X24)
% 0.23/0.48          | ~ (v5_orders_2 @ X24)
% 0.23/0.48          | ~ (l1_orders_2 @ X24)
% 0.23/0.48          | ~ (r2_hidden @ X27 @ (k4_orders_2 @ X24 @ X23))
% 0.23/0.48          | (m2_orders_2 @ X27 @ X24 @ X23)
% 0.23/0.48          | ~ (m1_orders_1 @ X23 @ (k1_orders_1 @ (u1_struct_0 @ X24))))),
% 0.23/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.23/0.48  thf('34', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.48          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.23/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.48          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.48          | (v2_struct_0 @ sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['31', '33'])).
% 0.23/0.48  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('36', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('38', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('39', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.48          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.23/0.48          | (v2_struct_0 @ sk_A))),
% 0.23/0.48      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.23/0.48  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('41', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.23/0.48          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.23/0.48      inference('clc', [status(thm)], ['39', '40'])).
% 0.23/0.48  thf('42', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.23/0.48      inference('sup-', [status(thm)], ['30', '41'])).
% 0.23/0.48  thf('43', plain,
% 0.23/0.48      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t79_orders_2, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48           ( ![C:$i]:
% 0.23/0.48             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.23/0.48               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.23/0.48  thf('44', plain,
% 0.23/0.48      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.23/0.48         (~ (m1_orders_1 @ X31 @ (k1_orders_1 @ (u1_struct_0 @ X32)))
% 0.23/0.48          | (r2_hidden @ (k1_funct_1 @ X31 @ (u1_struct_0 @ X32)) @ X33)
% 0.23/0.48          | ~ (m2_orders_2 @ X33 @ X32 @ X31)
% 0.23/0.48          | ~ (l1_orders_2 @ X32)
% 0.23/0.48          | ~ (v5_orders_2 @ X32)
% 0.23/0.48          | ~ (v4_orders_2 @ X32)
% 0.23/0.48          | ~ (v3_orders_2 @ X32)
% 0.23/0.48          | (v2_struct_0 @ X32))),
% 0.23/0.48      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.23/0.48  thf('45', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v2_struct_0 @ sk_A)
% 0.23/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.48          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.48          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.48          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.23/0.48  thf('46', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('47', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('48', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('50', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((v2_struct_0 @ sk_A)
% 0.23/0.48          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.23/0.48          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.23/0.48      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.23/0.48  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('52', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.23/0.48          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.23/0.48      inference('clc', [status(thm)], ['50', '51'])).
% 0.23/0.48  thf('53', plain,
% 0.23/0.48      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 0.23/0.48      inference('sup-', [status(thm)], ['42', '52'])).
% 0.23/0.48  thf(t113_zfmisc_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.48  thf('54', plain,
% 0.23/0.48      (![X11 : $i, X12 : $i]:
% 0.23/0.48         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.23/0.48          | ((X12) != (k1_xboole_0)))),
% 0.23/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.48  thf('55', plain,
% 0.23/0.48      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.48      inference('simplify', [status(thm)], ['54'])).
% 0.23/0.48  thf(t152_zfmisc_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.23/0.48  thf('56', plain,
% 0.23/0.48      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.23/0.48      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.23/0.48  thf('57', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.23/0.48  thf('58', plain, ($false), inference('sup-', [status(thm)], ['53', '57'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
