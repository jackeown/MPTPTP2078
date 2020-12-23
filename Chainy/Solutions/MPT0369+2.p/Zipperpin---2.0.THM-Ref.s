%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0369+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OK7PKyTWa6

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 5.71s
% Output     : Refutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  253 ( 404 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_21_type,type,(
    sk_C_21: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ A ) )
             => ( ~ ( r2_hidden @ ( C @ B ) )
               => ( r2_hidden @ ( C @ ( k3_subset_1 @ ( A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ ( C @ A ) )
               => ( ~ ( r2_hidden @ ( C @ B ) )
                 => ( r2_hidden @ ( C @ ( k3_subset_1 @ ( A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( sk_C_21 @ sk_B_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ ( sk_C_21 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X1469: $i,X1470: $i] :
      ( ~ ( m1_subset_1 @ ( X1469 @ X1470 ) )
      | ( r2_hidden @ ( X1469 @ X1470 ) )
      | ( v1_xboole_0 @ X1470 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A_2 )
    | ( r2_hidden @ ( sk_C_21 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('4',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('5',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference('simplify_reflect+',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_C_21 @ sk_A_2 ) ),
    inference(clc,[status(thm)],['3','11'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ~ ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ ( X29 @ X30 ) )
      | ( r2_hidden @ ( X29 @ X31 ) )
      | ( r2_hidden @ ( X29 @ X32 ) )
      | ( X32
       != ( k4_xboole_0 @ ( X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( X29 @ ( k4_xboole_0 @ ( X30 @ X31 ) ) ) )
      | ( r2_hidden @ ( X29 @ X31 ) )
      | ~ ( r2_hidden @ ( X29 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('15',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( X29 @ ( k6_subset_1 @ ( X30 @ X31 ) ) ) )
      | ( r2_hidden @ ( X29 @ X31 ) )
      | ~ ( r2_hidden @ ( X29 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_21 @ X0 ) )
      | ( r2_hidden @ ( sk_C_21 @ ( k6_subset_1 @ ( sk_A_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ ( sk_C_21 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k4_xboole_0 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( sk_C_21 @ ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_C_21 @ sk_B_8 ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
