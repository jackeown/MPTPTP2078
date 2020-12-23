%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1PKfqQ8AmX

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:06 EST 2020

% Result     : Theorem 5.78s
% Output     : Refutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 208 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :  906 (2085 expanded)
%              Number of equality atoms :   44 ( 156 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('2',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X24 @ X21 @ X22 ) @ ( sk_E_1 @ X24 @ X21 @ X22 ) @ X24 @ X21 @ X22 )
      | ( X23
       != ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X24 @ X21 @ X22 ) @ ( sk_E_1 @ X24 @ X21 @ X22 ) @ X24 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_A @ sk_B ) @ ( sk_E_1 @ X0 @ sk_A @ sk_B ) @ X0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) @ ( sk_E_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X12 @ X16 )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X32 ) )
      | ~ ( r2_hidden @ X30 @ X32 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) @ ( sk_E_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X32 ) )
      | ~ ( r2_hidden @ X30 @ X32 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_B ) @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X1 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_B @ sk_A )
      | ( r1_tarski @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_A )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','55'])).

thf('57',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('58',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X34 @ X33 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('59',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['59','60','61'])).

thf('63',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ),
    inference(clc,[status(thm)],['18','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('70',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['59','60','61'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1PKfqQ8AmX
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:45:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 5.78/6.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.78/6.01  % Solved by: fo/fo7.sh
% 5.78/6.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.78/6.01  % done 3160 iterations in 5.560s
% 5.78/6.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.78/6.01  % SZS output start Refutation
% 5.78/6.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.78/6.01  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 5.78/6.01  thf(sk_A_type, type, sk_A: $i).
% 5.78/6.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.78/6.01  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 5.78/6.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.78/6.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 5.78/6.01  thf(sk_B_type, type, sk_B: $i).
% 5.78/6.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.78/6.01  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.78/6.01  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.78/6.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.78/6.01  thf(d3_tarski, axiom,
% 5.78/6.01    (![A:$i,B:$i]:
% 5.78/6.01     ( ( r1_tarski @ A @ B ) <=>
% 5.78/6.01       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.78/6.01  thf('0', plain,
% 5.78/6.01      (![X1 : $i, X3 : $i]:
% 5.78/6.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.78/6.01      inference('cnf', [status(esa)], [d3_tarski])).
% 5.78/6.01  thf('1', plain,
% 5.78/6.01      (![X1 : $i, X3 : $i]:
% 5.78/6.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.78/6.01      inference('cnf', [status(esa)], [d3_tarski])).
% 5.78/6.01  thf(t114_zfmisc_1, conjecture,
% 5.78/6.01    (![A:$i,B:$i]:
% 5.78/6.01     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 5.78/6.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.78/6.01         ( ( A ) = ( B ) ) ) ))).
% 5.78/6.01  thf(zf_stmt_0, negated_conjecture,
% 5.78/6.01    (~( ![A:$i,B:$i]:
% 5.78/6.01        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 5.78/6.01          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.78/6.01            ( ( A ) = ( B ) ) ) ) )),
% 5.78/6.01    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 5.78/6.01  thf('2', plain,
% 5.78/6.01      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.78/6.01  thf(d2_zfmisc_1, axiom,
% 5.78/6.01    (![A:$i,B:$i,C:$i]:
% 5.78/6.01     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 5.78/6.01       ( ![D:$i]:
% 5.78/6.01         ( ( r2_hidden @ D @ C ) <=>
% 5.78/6.01           ( ?[E:$i,F:$i]:
% 5.78/6.01             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 5.78/6.01               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 5.78/6.01  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 5.78/6.01  thf(zf_stmt_2, axiom,
% 5.78/6.01    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 5.78/6.01     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 5.78/6.01       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 5.78/6.01         ( r2_hidden @ E @ A ) ) ))).
% 5.78/6.01  thf(zf_stmt_3, axiom,
% 5.78/6.01    (![A:$i,B:$i,C:$i]:
% 5.78/6.01     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 5.78/6.01       ( ![D:$i]:
% 5.78/6.01         ( ( r2_hidden @ D @ C ) <=>
% 5.78/6.01           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 5.78/6.01  thf('3', plain,
% 5.78/6.01      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 5.78/6.01         (~ (r2_hidden @ X24 @ X23)
% 5.78/6.01          | (zip_tseitin_0 @ (sk_F_1 @ X24 @ X21 @ X22) @ 
% 5.78/6.01             (sk_E_1 @ X24 @ X21 @ X22) @ X24 @ X21 @ X22)
% 5.78/6.01          | ((X23) != (k2_zfmisc_1 @ X22 @ X21)))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.78/6.01  thf('4', plain,
% 5.78/6.01      (![X21 : $i, X22 : $i, X24 : $i]:
% 5.78/6.01         ((zip_tseitin_0 @ (sk_F_1 @ X24 @ X21 @ X22) @ 
% 5.78/6.01           (sk_E_1 @ X24 @ X21 @ X22) @ X24 @ X21 @ X22)
% 5.78/6.01          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X22 @ X21)))),
% 5.78/6.01      inference('simplify', [status(thm)], ['3'])).
% 5.78/6.01  thf('5', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 5.78/6.01          | (zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_A @ sk_B) @ 
% 5.78/6.01             (sk_E_1 @ X0 @ sk_A @ sk_B) @ X0 @ sk_A @ sk_B))),
% 5.78/6.01      inference('sup-', [status(thm)], ['2', '4'])).
% 5.78/6.01  thf('6', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (zip_tseitin_0 @ 
% 5.78/6.01             (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B) @ 
% 5.78/6.01             (sk_E_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B) @ 
% 5.78/6.01             (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B))),
% 5.78/6.01      inference('sup-', [status(thm)], ['1', '5'])).
% 5.78/6.01  thf('7', plain,
% 5.78/6.01      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 5.78/6.01         ((r2_hidden @ X12 @ X16)
% 5.78/6.01          | ~ (zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.78/6.01  thf('8', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (r2_hidden @ 
% 5.78/6.01             (sk_E_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B) @ 
% 5.78/6.01             sk_B))),
% 5.78/6.01      inference('sup-', [status(thm)], ['6', '7'])).
% 5.78/6.01  thf(l54_zfmisc_1, axiom,
% 5.78/6.01    (![A:$i,B:$i,C:$i,D:$i]:
% 5.78/6.01     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 5.78/6.01       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 5.78/6.01  thf('9', plain,
% 5.78/6.01      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i]:
% 5.78/6.01         ((r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X32))
% 5.78/6.01          | ~ (r2_hidden @ X30 @ X32)
% 5.78/6.01          | ~ (r2_hidden @ X28 @ X29))),
% 5.78/6.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 5.78/6.01  thf('10', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | ~ (r2_hidden @ X2 @ X1)
% 5.78/6.01          | (r2_hidden @ 
% 5.78/6.01             (k4_tarski @ X2 @ 
% 5.78/6.01              (sk_E_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B)) @ 
% 5.78/6.01             (k2_zfmisc_1 @ X1 @ sk_B)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['8', '9'])).
% 5.78/6.01  thf('11', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.01         ((r1_tarski @ X0 @ X1)
% 5.78/6.01          | (r2_hidden @ 
% 5.78/6.01             (k4_tarski @ (sk_C @ X1 @ X0) @ 
% 5.78/6.01              (sk_E_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B)) @ 
% 5.78/6.01             (k2_zfmisc_1 @ X0 @ sk_B))
% 5.78/6.01          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X2))),
% 5.78/6.01      inference('sup-', [status(thm)], ['0', '10'])).
% 5.78/6.01  thf('12', plain,
% 5.78/6.01      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.78/6.01  thf('13', plain,
% 5.78/6.01      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 5.78/6.01         ((r2_hidden @ X28 @ X29)
% 5.78/6.01          | ~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X31)))),
% 5.78/6.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 5.78/6.01  thf('14', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 5.78/6.01          | (r2_hidden @ X1 @ sk_B))),
% 5.78/6.01      inference('sup-', [status(thm)], ['12', '13'])).
% 5.78/6.01  thf('15', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (r1_tarski @ sk_A @ X1)
% 5.78/6.01          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 5.78/6.01      inference('sup-', [status(thm)], ['11', '14'])).
% 5.78/6.01  thf('16', plain,
% 5.78/6.01      (![X1 : $i, X3 : $i]:
% 5.78/6.01         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.78/6.01      inference('cnf', [status(esa)], [d3_tarski])).
% 5.78/6.01  thf('17', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         ((r1_tarski @ sk_A @ sk_B)
% 5.78/6.01          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (r1_tarski @ sk_A @ sk_B))),
% 5.78/6.01      inference('sup-', [status(thm)], ['15', '16'])).
% 5.78/6.01  thf('18', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (r1_tarski @ sk_A @ sk_B))),
% 5.78/6.01      inference('simplify', [status(thm)], ['17'])).
% 5.78/6.01  thf('19', plain,
% 5.78/6.01      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.78/6.01  thf('20', plain,
% 5.78/6.01      (![X1 : $i, X3 : $i]:
% 5.78/6.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.78/6.01      inference('cnf', [status(esa)], [d3_tarski])).
% 5.78/6.01  thf('21', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (zip_tseitin_0 @ 
% 5.78/6.01             (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B) @ 
% 5.78/6.01             (sk_E_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B) @ 
% 5.78/6.01             (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B))),
% 5.78/6.01      inference('sup-', [status(thm)], ['1', '5'])).
% 5.78/6.01  thf('22', plain,
% 5.78/6.01      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 5.78/6.01         ((r2_hidden @ X13 @ X15)
% 5.78/6.01          | ~ (zip_tseitin_0 @ X13 @ X12 @ X14 @ X15 @ X16))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.78/6.01  thf('23', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (r2_hidden @ 
% 5.78/6.01             (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B) @ 
% 5.78/6.01             sk_A))),
% 5.78/6.01      inference('sup-', [status(thm)], ['21', '22'])).
% 5.78/6.01  thf('24', plain,
% 5.78/6.01      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i]:
% 5.78/6.01         ((r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X32))
% 5.78/6.01          | ~ (r2_hidden @ X30 @ X32)
% 5.78/6.01          | ~ (r2_hidden @ X28 @ X29))),
% 5.78/6.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 5.78/6.01  thf('25', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | ~ (r2_hidden @ X2 @ X1)
% 5.78/6.01          | (r2_hidden @ 
% 5.78/6.01             (k4_tarski @ X2 @ 
% 5.78/6.01              (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B)) @ 
% 5.78/6.01             (k2_zfmisc_1 @ X1 @ sk_A)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['23', '24'])).
% 5.78/6.01  thf('26', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.01         ((r1_tarski @ X0 @ X1)
% 5.78/6.01          | (r2_hidden @ 
% 5.78/6.01             (k4_tarski @ (sk_C @ X1 @ X0) @ 
% 5.78/6.01              (sk_F_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B)) @ 
% 5.78/6.01             (k2_zfmisc_1 @ X0 @ sk_A))
% 5.78/6.01          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X2))),
% 5.78/6.01      inference('sup-', [status(thm)], ['20', '25'])).
% 5.78/6.01  thf('27', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         ((r2_hidden @ 
% 5.78/6.01           (k4_tarski @ (sk_C @ X1 @ sk_B) @ 
% 5.78/6.01            (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_A @ sk_B)) @ 
% 5.78/6.01           (k2_zfmisc_1 @ sk_A @ sk_B))
% 5.78/6.01          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (r1_tarski @ sk_B @ X1))),
% 5.78/6.01      inference('sup+', [status(thm)], ['19', '26'])).
% 5.78/6.01  thf('28', plain,
% 5.78/6.01      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 5.78/6.01         ((r2_hidden @ X28 @ X29)
% 5.78/6.01          | ~ (r2_hidden @ (k4_tarski @ X28 @ X30) @ (k2_zfmisc_1 @ X29 @ X31)))),
% 5.78/6.01      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 5.78/6.01  thf('29', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         ((r1_tarski @ sk_B @ X1)
% 5.78/6.01          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (r2_hidden @ (sk_C @ X1 @ sk_B) @ sk_A))),
% 5.78/6.01      inference('sup-', [status(thm)], ['27', '28'])).
% 5.78/6.01  thf('30', plain,
% 5.78/6.01      (![X1 : $i, X3 : $i]:
% 5.78/6.01         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.78/6.01      inference('cnf', [status(esa)], [d3_tarski])).
% 5.78/6.01  thf('31', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.78/6.01          | (r1_tarski @ sk_B @ sk_A)
% 5.78/6.01          | (r1_tarski @ sk_B @ sk_A))),
% 5.78/6.01      inference('sup-', [status(thm)], ['29', '30'])).
% 5.78/6.01  thf('32', plain,
% 5.78/6.01      (![X0 : $i]:
% 5.78/6.01         ((r1_tarski @ sk_B @ sk_A)
% 5.78/6.01          | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 5.78/6.01      inference('simplify', [status(thm)], ['31'])).
% 5.78/6.01  thf('33', plain,
% 5.78/6.01      (![X1 : $i, X3 : $i]:
% 5.78/6.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.78/6.01      inference('cnf', [status(esa)], [d3_tarski])).
% 5.78/6.01  thf(t1_xboole_0, axiom,
% 5.78/6.01    (![A:$i,B:$i,C:$i]:
% 5.78/6.01     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 5.78/6.01       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 5.78/6.01  thf('34', plain,
% 5.78/6.01      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.78/6.01         ((r2_hidden @ X4 @ X5)
% 5.78/6.01          | (r2_hidden @ X4 @ X6)
% 5.78/6.01          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 5.78/6.01      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.78/6.01  thf('35', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.01         ((r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 5.78/6.01          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 5.78/6.01          | (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 5.78/6.01      inference('sup-', [status(thm)], ['33', '34'])).
% 5.78/6.01  thf('36', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         ((r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X0)
% 5.78/6.01          | (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 5.78/6.01      inference('eq_fact', [status(thm)], ['35'])).
% 5.78/6.01  thf('37', plain,
% 5.78/6.01      (![X1 : $i, X3 : $i]:
% 5.78/6.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.78/6.01      inference('cnf', [status(esa)], [d3_tarski])).
% 5.78/6.01  thf('38', plain,
% 5.78/6.01      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.78/6.01         (~ (r2_hidden @ X4 @ X5)
% 5.78/6.01          | ~ (r2_hidden @ X4 @ X6)
% 5.78/6.01          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 5.78/6.01      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.78/6.01  thf('39', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.01         ((r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 5.78/6.01          | ~ (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 5.78/6.01          | ~ (r2_hidden @ (sk_C @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 5.78/6.01      inference('sup-', [status(thm)], ['37', '38'])).
% 5.78/6.01  thf('40', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         ((r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 5.78/6.01          | ~ (r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X0)
% 5.78/6.01          | (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 5.78/6.01      inference('sup-', [status(thm)], ['36', '39'])).
% 5.78/6.01  thf('41', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         (~ (r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X0)
% 5.78/6.01          | (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 5.78/6.01      inference('simplify', [status(thm)], ['40'])).
% 5.78/6.01  thf('42', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         ((r2_hidden @ (sk_C @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X0)
% 5.78/6.01          | (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 5.78/6.01      inference('eq_fact', [status(thm)], ['35'])).
% 5.78/6.01  thf('43', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 5.78/6.01      inference('clc', [status(thm)], ['41', '42'])).
% 5.78/6.01  thf('44', plain,
% 5.78/6.01      (![X1 : $i, X3 : $i]:
% 5.78/6.01         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.78/6.01      inference('cnf', [status(esa)], [d3_tarski])).
% 5.78/6.01  thf(t5_boole, axiom,
% 5.78/6.01    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.78/6.01  thf('45', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 5.78/6.01      inference('cnf', [status(esa)], [t5_boole])).
% 5.78/6.01  thf('46', plain,
% 5.78/6.01      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.78/6.01         (~ (r2_hidden @ X4 @ X5)
% 5.78/6.01          | ~ (r2_hidden @ X4 @ X6)
% 5.78/6.01          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 5.78/6.01      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.78/6.01  thf('47', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         (~ (r2_hidden @ X1 @ X0)
% 5.78/6.01          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 5.78/6.01          | ~ (r2_hidden @ X1 @ X0))),
% 5.78/6.01      inference('sup-', [status(thm)], ['45', '46'])).
% 5.78/6.01  thf('48', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 5.78/6.01      inference('simplify', [status(thm)], ['47'])).
% 5.78/6.01  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.78/6.01      inference('condensation', [status(thm)], ['48'])).
% 5.78/6.01  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.78/6.01      inference('sup-', [status(thm)], ['44', '49'])).
% 5.78/6.01  thf(d10_xboole_0, axiom,
% 5.78/6.01    (![A:$i,B:$i]:
% 5.78/6.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.78/6.01  thf('51', plain,
% 5.78/6.01      (![X8 : $i, X10 : $i]:
% 5.78/6.01         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 5.78/6.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.78/6.01  thf('52', plain,
% 5.78/6.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['50', '51'])).
% 5.78/6.01  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.78/6.01      inference('sup-', [status(thm)], ['43', '52'])).
% 5.78/6.01  thf('54', plain,
% 5.78/6.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['50', '51'])).
% 5.78/6.01  thf('55', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['53', '54'])).
% 5.78/6.01  thf('56', plain,
% 5.78/6.01      (((r1_tarski @ sk_B @ sk_A)
% 5.78/6.01        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['32', '55'])).
% 5.78/6.01  thf('57', plain,
% 5.78/6.01      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.78/6.01  thf(t113_zfmisc_1, axiom,
% 5.78/6.01    (![A:$i,B:$i]:
% 5.78/6.01     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.78/6.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.78/6.01  thf('58', plain,
% 5.78/6.01      (![X33 : $i, X34 : $i]:
% 5.78/6.01         (((X33) = (k1_xboole_0))
% 5.78/6.01          | ((X34) = (k1_xboole_0))
% 5.78/6.01          | ((k2_zfmisc_1 @ X34 @ X33) != (k1_xboole_0)))),
% 5.78/6.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.78/6.01  thf('59', plain,
% 5.78/6.01      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 5.78/6.01        | ((sk_B) = (k1_xboole_0))
% 5.78/6.01        | ((sk_A) = (k1_xboole_0)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['57', '58'])).
% 5.78/6.01  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.78/6.01  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.78/6.01  thf('62', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 5.78/6.01      inference('simplify_reflect-', [status(thm)], ['59', '60', '61'])).
% 5.78/6.01  thf('63', plain, ((r1_tarski @ sk_B @ sk_A)),
% 5.78/6.01      inference('simplify_reflect-', [status(thm)], ['56', '62'])).
% 5.78/6.01  thf('64', plain,
% 5.78/6.01      (![X8 : $i, X10 : $i]:
% 5.78/6.01         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 5.78/6.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.78/6.01  thf('65', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['63', '64'])).
% 5.78/6.01  thf('66', plain, (((sk_A) != (sk_B))),
% 5.78/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.78/6.01  thf('67', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 5.78/6.01      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 5.78/6.01  thf('68', plain,
% 5.78/6.01      (![X0 : $i]: (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)),
% 5.78/6.01      inference('clc', [status(thm)], ['18', '67'])).
% 5.78/6.01  thf('69', plain,
% 5.78/6.01      (![X0 : $i, X1 : $i]:
% 5.78/6.01         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 5.78/6.01      inference('sup-', [status(thm)], ['53', '54'])).
% 5.78/6.01  thf('70', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 5.78/6.01      inference('sup-', [status(thm)], ['68', '69'])).
% 5.78/6.01  thf('71', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 5.78/6.01      inference('simplify_reflect-', [status(thm)], ['59', '60', '61'])).
% 5.78/6.01  thf('72', plain, ($false),
% 5.78/6.01      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 5.78/6.01  
% 5.78/6.01  % SZS output end Refutation
% 5.78/6.01  
% 5.84/6.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
