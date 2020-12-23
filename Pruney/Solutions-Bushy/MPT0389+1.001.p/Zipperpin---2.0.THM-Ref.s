%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7AtHImcJMc

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:49 EST 2020

% Result     : Theorem 11.58s
% Output     : Refutation 11.58s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  443 ( 656 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf(t7_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( A = k1_xboole_0 )
          | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_setfam_1])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ ( k1_setfam_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X7: $i] :
      ( ( X2
       != ( k1_setfam_1 @ X3 ) )
      | ( r2_hidden @ X7 @ X2 )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X3 ) @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('13',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X3 ) @ X3 )
      | ( r2_hidden @ X7 @ ( k1_setfam_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( X2
       != ( k1_setfam_1 @ X3 ) )
      | ~ ( r2_hidden @ X5 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X2 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('22',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ X3 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X5 @ X3 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_setfam_1 @ sk_B_1 ) ) @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i,X7: $i] :
      ( ( X2
       != ( k1_setfam_1 @ X3 ) )
      | ( r2_hidden @ X7 @ X2 )
      | ~ ( r2_hidden @ X7 @ ( sk_D_1 @ X7 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('26',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r2_hidden @ X7 @ ( sk_D_1 @ X7 @ X3 ) )
      | ( r2_hidden @ X7 @ ( k1_setfam_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_setfam_1 @ sk_B_1 ) ) @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_setfam_1 @ sk_B_1 ) ) @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_setfam_1 @ sk_B_1 ) ) @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_setfam_1 @ sk_B_1 ) ) @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X12 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X10 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_setfam_1 @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X8: $i] :
      ( ( X8
       != ( k1_setfam_1 @ X3 ) )
      | ( X8 = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('37',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('38',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('39',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('41',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['11','35','37','42'])).


%------------------------------------------------------------------------------
