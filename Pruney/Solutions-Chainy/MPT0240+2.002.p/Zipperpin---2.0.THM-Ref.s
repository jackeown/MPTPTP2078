%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.16IlbfcIbr

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:07 EST 2020

% Result     : Theorem 18.76s
% Output     : Refutation 18.76s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 548 expanded)
%              Number of leaves         :   18 ( 165 expanded)
%              Depth                    :   28
%              Number of atoms          : 1803 (7152 expanded)
%              Number of equality atoms :  150 ( 711 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf(zf_stmt_0,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ( X8
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X6 @ X11 )
      | ( zip_tseitin_0 @ X7 @ X6 @ ( k4_tarski @ X6 @ X7 ) @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ ( k4_tarski @ X2 @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X0 @ X1 @ ( k4_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ( X19
        = ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X19 @ X15 @ X16 ) @ ( sk_E @ X19 @ X15 @ X16 ) @ ( sk_D @ X19 @ X15 @ X16 ) @ X15 @ X16 )
      | ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X6 @ X10 )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( ( sk_E @ X2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ ( k1_tarski @ X0 ) @ X2 @ X1 ) @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X2 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_E @ ( k1_tarski @ X2 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19
        = ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ ( sk_D @ X19 @ X15 @ X16 ) @ X15 @ X16 )
      | ~ ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( zip_tseitin_0 @ X4 @ X3 @ X0 @ X2 @ ( k1_tarski @ X1 ) )
      | ( ( sk_E @ ( k1_tarski @ X0 ) @ X2 @ ( k1_tarski @ X1 ) )
        = X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ ( k1_tarski @ X1 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ ( k1_tarski @ X1 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X2 ) )
      | ( ( sk_E @ ( k1_tarski @ X0 ) @ X2 @ ( k1_tarski @ X1 ) )
        = X1 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X0 @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( sk_E @ ( k1_tarski @ X0 ) @ X2 @ ( k1_tarski @ X1 ) )
        = X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X2 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X0 @ X2 @ ( k1_tarski @ X1 ) )
      | ( ( sk_E @ ( k1_tarski @ X0 ) @ X2 @ ( k1_tarski @ X1 ) )
        = X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( zip_tseitin_0 @ X4 @ X3 @ X0 @ X2 @ ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X2 ) )
      | ( ( sk_E @ ( k1_tarski @ X0 ) @ X2 @ ( k1_tarski @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_E @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_E @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = X1 )
      | ( ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ( X19
        = ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X19 @ X15 @ X16 ) @ ( sk_E @ X19 @ X15 @ X16 ) @ ( sk_D @ X19 @ X15 @ X16 ) @ X15 @ X16 )
      | ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X9 )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
      | ( ( sk_F @ X2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X2 ) @ X1 )
        = X2 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X2 ) ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X2 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X2 ) @ X1 )
        = X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X2 ) ) )
      | ( ( sk_F @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X2 ) @ X1 )
        = X2 ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) @ X2 )
        = X1 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_zfmisc_1 @ X2 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) @ X2 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['32','43'])).

thf(t35_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_zfmisc_1])).

thf('45',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
       != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = X0 )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('57',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ ( k1_tarski @ X0 ) @ X2 @ X1 ) @ X2 )
      | ( ( k1_tarski @ X0 )
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( ( sk_F @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_F @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) @ X2 )
        = X0 )
      | ( ( k1_tarski @ X1 )
        = ( k2_zfmisc_1 @ X2 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( k1_tarski @ X2 )
        = ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X2 ) ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X2 )
      | ( ( sk_F @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( X3 = X2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ X1 @ X0 )
        = X2 )
      | ( ( sk_F @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = X0 )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B ) ) ),
    inference(clc,[status(thm)],['47','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = X0 )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['30','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = X0 )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['30','66'])).

thf('69',plain,(
    ! [X15: $i,X16: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19
        = ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ ( sk_D @ X19 @ X15 @ X16 ) @ X15 @ X16 )
      | ~ ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('73',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
      | ( ( sk_F @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( sk_F @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = sk_B )
    | ( ( k2_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','76'])).

thf('78',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('79',plain,
    ( ( ( sk_F @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = sk_B )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('81',plain,
    ( ( sk_F @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ( X19
        = ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X19 @ X15 @ X16 ) @ ( sk_E @ X19 @ X15 @ X16 ) @ ( sk_D @ X19 @ X15 @ X16 ) @ X15 @ X16 )
      | ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8
        = ( k4_tarski @ X6 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ X2 @ X1 @ X0 )
        = ( k4_tarski @ ( sk_E @ X2 @ X1 @ X0 ) @ ( sk_F @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ ( sk_E @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ sk_B ) )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ ( sk_E @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('89',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ ( sk_E @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ sk_B ) )
    | ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_B ) ) )
    | ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','89'])).

thf('91',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('92',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    | ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('95',plain,
    ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X15: $i,X16: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19
        = ( k2_zfmisc_1 @ X16 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ ( sk_D @ X19 @ X15 @ X16 ) @ X15 @ X16 )
      | ~ ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
        = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_D @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k4_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
        = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k4_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.16IlbfcIbr
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.76/18.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.76/18.94  % Solved by: fo/fo7.sh
% 18.76/18.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.76/18.94  % done 2881 iterations in 18.480s
% 18.76/18.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.76/18.94  % SZS output start Refutation
% 18.76/18.94  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 18.76/18.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 18.76/18.94  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 18.76/18.94  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 18.76/18.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 18.76/18.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 18.76/18.94  thf(sk_A_type, type, sk_A: $i).
% 18.76/18.94  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 18.76/18.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 18.76/18.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 18.76/18.94  thf(sk_B_type, type, sk_B: $i).
% 18.76/18.94  thf(d1_tarski, axiom,
% 18.76/18.94    (![A:$i,B:$i]:
% 18.76/18.94     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 18.76/18.94       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 18.76/18.94  thf('0', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 18.76/18.94      inference('cnf', [status(esa)], [d1_tarski])).
% 18.76/18.94  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 18.76/18.94      inference('simplify', [status(thm)], ['0'])).
% 18.76/18.94  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 18.76/18.94      inference('simplify', [status(thm)], ['0'])).
% 18.76/18.94  thf(d2_zfmisc_1, axiom,
% 18.76/18.94    (![A:$i,B:$i,C:$i]:
% 18.76/18.94     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 18.76/18.94       ( ![D:$i]:
% 18.76/18.94         ( ( r2_hidden @ D @ C ) <=>
% 18.76/18.94           ( ?[E:$i,F:$i]:
% 18.76/18.94             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 18.76/18.94               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 18.76/18.94  thf(zf_stmt_0, axiom,
% 18.76/18.94    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 18.76/18.94     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 18.76/18.94       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 18.76/18.94         ( r2_hidden @ E @ A ) ) ))).
% 18.76/18.94  thf('3', plain,
% 18.76/18.94      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 18.76/18.94         ((zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X11)
% 18.76/18.94          | ~ (r2_hidden @ X6 @ X11)
% 18.76/18.94          | ~ (r2_hidden @ X7 @ X9)
% 18.76/18.94          | ((X8) != (k4_tarski @ X6 @ X7)))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.94  thf('4', plain,
% 18.76/18.94      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i]:
% 18.76/18.94         (~ (r2_hidden @ X7 @ X9)
% 18.76/18.94          | ~ (r2_hidden @ X6 @ X11)
% 18.76/18.94          | (zip_tseitin_0 @ X7 @ X6 @ (k4_tarski @ X6 @ X7) @ X9 @ X11))),
% 18.76/18.94      inference('simplify', [status(thm)], ['3'])).
% 18.76/18.94  thf('5', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         ((zip_tseitin_0 @ X0 @ X2 @ (k4_tarski @ X2 @ X0) @ 
% 18.76/18.94           (k1_tarski @ X0) @ X1)
% 18.76/18.94          | ~ (r2_hidden @ X2 @ X1))),
% 18.76/18.94      inference('sup-', [status(thm)], ['2', '4'])).
% 18.76/18.94  thf('6', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ (k1_tarski @ X1) @ 
% 18.76/18.94          (k1_tarski @ X0))),
% 18.76/18.94      inference('sup-', [status(thm)], ['1', '5'])).
% 18.76/18.94  thf(t69_enumset1, axiom,
% 18.76/18.94    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 18.76/18.94  thf('7', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('8', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('9', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ (k1_tarski @ X1) @ 
% 18.76/18.94          (k1_tarski @ X0))),
% 18.76/18.94      inference('sup-', [status(thm)], ['1', '5'])).
% 18.76/18.94  thf('10', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (zip_tseitin_0 @ X0 @ X1 @ (k4_tarski @ X1 @ X0) @ 
% 18.76/18.94          (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1))),
% 18.76/18.94      inference('sup+', [status(thm)], ['8', '9'])).
% 18.76/18.94  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 18.76/18.94  thf(zf_stmt_2, axiom,
% 18.76/18.94    (![A:$i,B:$i,C:$i]:
% 18.76/18.94     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 18.76/18.94       ( ![D:$i]:
% 18.76/18.94         ( ( r2_hidden @ D @ C ) <=>
% 18.76/18.94           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 18.76/18.94  thf('11', plain,
% 18.76/18.94      (![X15 : $i, X16 : $i, X19 : $i]:
% 18.76/18.94         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 18.76/18.94          | (zip_tseitin_0 @ (sk_F @ X19 @ X15 @ X16) @ 
% 18.76/18.94             (sk_E @ X19 @ X15 @ X16) @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 18.76/18.94          | (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.76/18.94  thf('12', plain,
% 18.76/18.94      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 18.76/18.94         ((r2_hidden @ X6 @ X10) | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.94  thf('13', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 18.76/18.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 18.76/18.94          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 18.76/18.94      inference('sup-', [status(thm)], ['11', '12'])).
% 18.76/18.94  thf('14', plain,
% 18.76/18.94      (![X0 : $i, X2 : $i, X3 : $i]:
% 18.76/18.94         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 18.76/18.94      inference('cnf', [status(esa)], [d1_tarski])).
% 18.76/18.94  thf('15', plain,
% 18.76/18.94      (![X0 : $i, X3 : $i]:
% 18.76/18.94         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['14'])).
% 18.76/18.94  thf('16', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((X2) = (k2_zfmisc_1 @ (k1_tarski @ X0) @ X1))
% 18.76/18.94          | (r2_hidden @ (sk_D @ X2 @ X1 @ (k1_tarski @ X0)) @ X2)
% 18.76/18.94          | ((sk_E @ X2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['13', '15'])).
% 18.76/18.94  thf('17', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 18.76/18.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 18.76/18.94          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 18.76/18.94      inference('sup-', [status(thm)], ['11', '12'])).
% 18.76/18.94  thf('18', plain,
% 18.76/18.94      (![X0 : $i, X3 : $i]:
% 18.76/18.94         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['14'])).
% 18.76/18.94  thf('19', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         ((r2_hidden @ (sk_E @ (k1_tarski @ X0) @ X2 @ X1) @ X1)
% 18.76/18.94          | ((k1_tarski @ X0) = (k2_zfmisc_1 @ X1 @ X2))
% 18.76/18.94          | ((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['17', '18'])).
% 18.76/18.94  thf('20', plain,
% 18.76/18.94      (![X0 : $i, X3 : $i]:
% 18.76/18.94         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['14'])).
% 18.76/18.94  thf('21', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((sk_D @ (k1_tarski @ X2) @ X1 @ (k1_tarski @ X0)) = (X2))
% 18.76/18.94          | ((k1_tarski @ X2) = (k2_zfmisc_1 @ (k1_tarski @ X0) @ X1))
% 18.76/18.94          | ((sk_E @ (k1_tarski @ X2) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['19', '20'])).
% 18.76/18.94  thf('22', plain,
% 18.76/18.94      (![X15 : $i, X16 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 18.76/18.94         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X20 @ X21 @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 18.76/18.94          | ~ (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.76/18.94  thf('23', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.76/18.94         (~ (zip_tseitin_0 @ X4 @ X3 @ X0 @ X2 @ (k1_tarski @ X1))
% 18.76/18.94          | ((sk_E @ (k1_tarski @ X0) @ X2 @ (k1_tarski @ X1)) = (X1))
% 18.76/18.94          | ((k1_tarski @ X0) = (k2_zfmisc_1 @ (k1_tarski @ X1) @ X2))
% 18.76/18.94          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X2 @ (k1_tarski @ X1)) @ 
% 18.76/18.94               (k1_tarski @ X0))
% 18.76/18.94          | ((k1_tarski @ X0) = (k2_zfmisc_1 @ (k1_tarski @ X1) @ X2)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['21', '22'])).
% 18.76/18.94  thf('24', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.76/18.94         (~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X2 @ (k1_tarski @ X1)) @ 
% 18.76/18.94             (k1_tarski @ X0))
% 18.76/18.94          | ((k1_tarski @ X0) = (k2_zfmisc_1 @ (k1_tarski @ X1) @ X2))
% 18.76/18.94          | ((sk_E @ (k1_tarski @ X0) @ X2 @ (k1_tarski @ X1)) = (X1))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X4 @ X3 @ X0 @ X2 @ (k1_tarski @ X1)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['23'])).
% 18.76/18.94  thf('25', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.76/18.94         (((sk_E @ (k1_tarski @ X0) @ X2 @ (k1_tarski @ X1)) = (X1))
% 18.76/18.94          | ((k1_tarski @ X0) = (k2_zfmisc_1 @ (k1_tarski @ X1) @ X2))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X4 @ X3 @ X0 @ X2 @ (k1_tarski @ X1))
% 18.76/18.94          | ((sk_E @ (k1_tarski @ X0) @ X2 @ (k1_tarski @ X1)) = (X1))
% 18.76/18.94          | ((k1_tarski @ X0) = (k2_zfmisc_1 @ (k1_tarski @ X1) @ X2)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['16', '24'])).
% 18.76/18.94  thf('26', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.76/18.94         (~ (zip_tseitin_0 @ X4 @ X3 @ X0 @ X2 @ (k1_tarski @ X1))
% 18.76/18.94          | ((k1_tarski @ X0) = (k2_zfmisc_1 @ (k1_tarski @ X1) @ X2))
% 18.76/18.94          | ((sk_E @ (k1_tarski @ X0) @ X2 @ (k1_tarski @ X1)) = (X1)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['25'])).
% 18.76/18.94  thf('27', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (((sk_E @ (k1_tarski @ (k4_tarski @ X0 @ X1)) @ 
% 18.76/18.94            (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)) = (X0))
% 18.76/18.94          | ((k1_tarski @ (k4_tarski @ X0 @ X1))
% 18.76/18.94              = (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X1))))),
% 18.76/18.94      inference('sup-', [status(thm)], ['10', '26'])).
% 18.76/18.94  thf('28', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (((sk_E @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ (k1_tarski @ X0) @ 
% 18.76/18.94            (k1_tarski @ X1)) = (X1))
% 18.76/18.94          | ((k1_tarski @ (k4_tarski @ X1 @ X0))
% 18.76/18.94              = (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))))),
% 18.76/18.94      inference('sup+', [status(thm)], ['7', '27'])).
% 18.76/18.94  thf('29', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ (k1_tarski @ X1) @ 
% 18.76/18.94          (k1_tarski @ X0))),
% 18.76/18.94      inference('sup-', [status(thm)], ['1', '5'])).
% 18.76/18.94  thf('30', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('31', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('32', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('33', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('34', plain,
% 18.76/18.94      (![X15 : $i, X16 : $i, X19 : $i]:
% 18.76/18.94         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 18.76/18.94          | (zip_tseitin_0 @ (sk_F @ X19 @ X15 @ X16) @ 
% 18.76/18.94             (sk_E @ X19 @ X15 @ X16) @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 18.76/18.94          | (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.76/18.94  thf('35', plain,
% 18.76/18.94      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 18.76/18.94         ((r2_hidden @ X7 @ X9) | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.94  thf('36', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 18.76/18.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 18.76/18.94          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 18.76/18.94      inference('sup-', [status(thm)], ['34', '35'])).
% 18.76/18.94  thf('37', plain,
% 18.76/18.94      (![X0 : $i, X3 : $i]:
% 18.76/18.94         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['14'])).
% 18.76/18.94  thf('38', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((X2) = (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0)))
% 18.76/18.94          | (r2_hidden @ (sk_D @ X2 @ (k1_tarski @ X0) @ X1) @ X2)
% 18.76/18.94          | ((sk_F @ X2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['36', '37'])).
% 18.76/18.94  thf('39', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('40', plain,
% 18.76/18.94      (![X0 : $i, X3 : $i]:
% 18.76/18.94         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['14'])).
% 18.76/18.94  thf('41', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['39', '40'])).
% 18.76/18.94  thf('42', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((sk_F @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X2) @ X1) = (X2))
% 18.76/18.94          | ((k2_tarski @ X0 @ X0) = (k2_zfmisc_1 @ X1 @ (k1_tarski @ X2)))
% 18.76/18.94          | ((sk_D @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X2) @ X1) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['38', '41'])).
% 18.76/18.94  thf('43', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X2) @ X1) = (X0))
% 18.76/18.94          | ((k2_tarski @ X0 @ X0) = (k2_zfmisc_1 @ X1 @ (k1_tarski @ X2)))
% 18.76/18.94          | ((sk_F @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X2) @ X1) = (X2)))),
% 18.76/18.94      inference('sup+', [status(thm)], ['33', '42'])).
% 18.76/18.94  thf('44', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ X2) = (X1))
% 18.76/18.94          | ((k2_tarski @ X0 @ X0) = (k2_zfmisc_1 @ X2 @ (k1_tarski @ X1)))
% 18.76/18.94          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X1) @ X2) = (X0)))),
% 18.76/18.94      inference('sup+', [status(thm)], ['32', '43'])).
% 18.76/18.94  thf(t35_zfmisc_1, conjecture,
% 18.76/18.94    (![A:$i,B:$i]:
% 18.76/18.94     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 18.76/18.94       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 18.76/18.94  thf(zf_stmt_3, negated_conjecture,
% 18.76/18.94    (~( ![A:$i,B:$i]:
% 18.76/18.94        ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 18.76/18.94          ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )),
% 18.76/18.94    inference('cnf.neg', [status(esa)], [t35_zfmisc_1])).
% 18.76/18.94  thf('45', plain,
% 18.76/18.94      (((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 18.76/18.94         != (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.76/18.94  thf('46', plain,
% 18.76/18.94      (![X0 : $i]:
% 18.76/18.94         (((k2_tarski @ X0 @ X0) != (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 18.76/18.94          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (X0))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['44', '45'])).
% 18.76/18.94  thf('47', plain,
% 18.76/18.94      (![X0 : $i]:
% 18.76/18.94         (((k1_tarski @ X0) != (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B))
% 18.76/18.94          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['31', '46'])).
% 18.76/18.94  thf('48', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('49', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ X0 @ X1) @ (k1_tarski @ X1) @ 
% 18.76/18.94          (k1_tarski @ X0))),
% 18.76/18.94      inference('sup-', [status(thm)], ['1', '5'])).
% 18.76/18.94  thf('50', plain,
% 18.76/18.94      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 18.76/18.94         (~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 18.76/18.94          | (r2_hidden @ X14 @ X17)
% 18.76/18.94          | ((X17) != (k2_zfmisc_1 @ X16 @ X15)))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.76/18.94  thf('51', plain,
% 18.76/18.94      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 18.76/18.94         ((r2_hidden @ X14 @ (k2_zfmisc_1 @ X16 @ X15))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 18.76/18.94      inference('simplify', [status(thm)], ['50'])).
% 18.76/18.94  thf('52', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 18.76/18.94          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['49', '51'])).
% 18.76/18.94  thf('53', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 18.76/18.94          (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 18.76/18.94      inference('sup+', [status(thm)], ['48', '52'])).
% 18.76/18.94  thf('54', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('55', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('56', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 18.76/18.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 18.76/18.94          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 18.76/18.94      inference('sup-', [status(thm)], ['34', '35'])).
% 18.76/18.94  thf('57', plain,
% 18.76/18.94      (![X0 : $i, X3 : $i]:
% 18.76/18.94         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['14'])).
% 18.76/18.94  thf('58', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         ((r2_hidden @ (sk_F @ (k1_tarski @ X0) @ X2 @ X1) @ X2)
% 18.76/18.94          | ((k1_tarski @ X0) = (k2_zfmisc_1 @ X1 @ X2))
% 18.76/18.94          | ((sk_D @ (k1_tarski @ X0) @ X2 @ X1) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['56', '57'])).
% 18.76/18.94  thf('59', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['39', '40'])).
% 18.76/18.94  thf('60', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((sk_D @ (k1_tarski @ X2) @ (k2_tarski @ X0 @ X0) @ X1) = (X2))
% 18.76/18.94          | ((k1_tarski @ X2) = (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X2) @ (k2_tarski @ X0 @ X0) @ X1) = (X0)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['58', '59'])).
% 18.76/18.94  thf('61', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((sk_D @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2) = (X1))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0) @ X2) = (X0))
% 18.76/18.94          | ((k1_tarski @ X1) = (k2_zfmisc_1 @ X2 @ (k2_tarski @ X0 @ X0))))),
% 18.76/18.94      inference('sup+', [status(thm)], ['55', '60'])).
% 18.76/18.94  thf('62', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((sk_F @ (k1_tarski @ X2) @ (k1_tarski @ X0) @ X1) = (X0))
% 18.76/18.94          | ((k1_tarski @ X2) = (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 18.76/18.94          | ((sk_D @ (k1_tarski @ X2) @ (k1_tarski @ X0) @ X1) = (X2)))),
% 18.76/18.94      inference('sup+', [status(thm)], ['54', '61'])).
% 18.76/18.94  thf('63', plain,
% 18.76/18.94      (![X0 : $i, X3 : $i]:
% 18.76/18.94         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['14'])).
% 18.76/18.94  thf('64', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 18.76/18.94         (~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 18.76/18.94          | ((sk_D @ (k1_tarski @ X2) @ (k1_tarski @ X0) @ X1) = (X2))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X2) @ (k1_tarski @ X0) @ X1) = (X0))
% 18.76/18.94          | ((X3) = (X2)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['62', '63'])).
% 18.76/18.94  thf('65', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((k4_tarski @ X1 @ X0) = (X2))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X2) @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 18.76/18.94              = (X0))
% 18.76/18.94          | ((sk_D @ (k1_tarski @ X2) @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 18.76/18.94              = (X2)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['53', '64'])).
% 18.76/18.94  thf('66', plain,
% 18.76/18.94      (![X0 : $i]:
% 18.76/18.94         (((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94            = (X0))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B)))),
% 18.76/18.94      inference('clc', [status(thm)], ['47', '65'])).
% 18.76/18.94  thf('67', plain,
% 18.76/18.94      (![X0 : $i]:
% 18.76/18.94         (((sk_D @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ sk_B) @ 
% 18.76/18.94            (k1_tarski @ sk_A)) = (X0))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B)))),
% 18.76/18.94      inference('sup+', [status(thm)], ['30', '66'])).
% 18.76/18.94  thf('68', plain,
% 18.76/18.94      (![X0 : $i]:
% 18.76/18.94         (((sk_D @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ sk_B) @ 
% 18.76/18.94            (k1_tarski @ sk_A)) = (X0))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B)))),
% 18.76/18.94      inference('sup+', [status(thm)], ['30', '66'])).
% 18.76/18.94  thf('69', plain,
% 18.76/18.94      (![X15 : $i, X16 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 18.76/18.94         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X20 @ X21 @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 18.76/18.94          | ~ (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.76/18.94  thf('70', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ (k1_tarski @ sk_B) @ 
% 18.76/18.94             (k1_tarski @ sk_A))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B))
% 18.76/18.94          | ~ (r2_hidden @ 
% 18.76/18.94               (sk_D @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ sk_B) @ 
% 18.76/18.94                (k1_tarski @ sk_A)) @ 
% 18.76/18.94               (k2_tarski @ X0 @ X0))
% 18.76/18.94          | ((k2_tarski @ X0 @ X0)
% 18.76/18.94              = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 18.76/18.94      inference('sup-', [status(thm)], ['68', '69'])).
% 18.76/18.94  thf('71', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (~ (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B))
% 18.76/18.94          | ((k2_tarski @ X0 @ X0)
% 18.76/18.94              = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ (k1_tarski @ sk_B) @ 
% 18.76/18.94               (k1_tarski @ sk_A)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['67', '70'])).
% 18.76/18.94  thf('72', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('73', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 18.76/18.94      inference('simplify', [status(thm)], ['0'])).
% 18.76/18.94  thf('74', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 18.76/18.94      inference('sup+', [status(thm)], ['72', '73'])).
% 18.76/18.94  thf('75', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94            = (sk_B))
% 18.76/18.94          | ((k2_tarski @ X0 @ X0)
% 18.76/18.94              = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ (k1_tarski @ sk_B) @ 
% 18.76/18.94               (k1_tarski @ sk_A)))),
% 18.76/18.94      inference('demod', [status(thm)], ['71', '74'])).
% 18.76/18.94  thf('76', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         (~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ (k1_tarski @ sk_B) @ 
% 18.76/18.94             (k1_tarski @ sk_A))
% 18.76/18.94          | ((k2_tarski @ X0 @ X0)
% 18.76/18.94              = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 18.76/18.94          | ((sk_F @ (k1_tarski @ X0) @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94              = (sk_B)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['75'])).
% 18.76/18.94  thf('77', plain,
% 18.76/18.94      ((((sk_F @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94          (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (sk_B))
% 18.76/18.94        | ((k2_tarski @ (k4_tarski @ sk_A @ sk_B) @ (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94            = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 18.76/18.94      inference('sup-', [status(thm)], ['29', '76'])).
% 18.76/18.94  thf('78', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('79', plain,
% 18.76/18.94      ((((sk_F @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94          (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (sk_B))
% 18.76/18.94        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94            = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 18.76/18.94      inference('demod', [status(thm)], ['77', '78'])).
% 18.76/18.94  thf('80', plain,
% 18.76/18.94      (((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 18.76/18.94         != (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.76/18.94  thf('81', plain,
% 18.76/18.94      (((sk_F @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ (k1_tarski @ sk_B) @ 
% 18.76/18.94         (k1_tarski @ sk_A)) = (sk_B))),
% 18.76/18.94      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 18.76/18.94  thf('82', plain,
% 18.76/18.94      (![X15 : $i, X16 : $i, X19 : $i]:
% 18.76/18.94         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 18.76/18.94          | (zip_tseitin_0 @ (sk_F @ X19 @ X15 @ X16) @ 
% 18.76/18.94             (sk_E @ X19 @ X15 @ X16) @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 18.76/18.94          | (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.76/18.94  thf('83', plain,
% 18.76/18.94      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 18.76/18.94         (((X8) = (k4_tarski @ X6 @ X7))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X7 @ X6 @ X8 @ X9 @ X10))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.76/18.94  thf('84', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.76/18.94         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 18.76/18.94          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 18.76/18.94          | ((sk_D @ X2 @ X1 @ X0)
% 18.76/18.94              = (k4_tarski @ (sk_E @ X2 @ X1 @ X0) @ (sk_F @ X2 @ X1 @ X0))))),
% 18.76/18.94      inference('sup-', [status(thm)], ['82', '83'])).
% 18.76/18.94  thf('85', plain,
% 18.76/18.94      ((((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94          (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94          = (k4_tarski @ 
% 18.76/18.94             (sk_E @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94              (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 18.76/18.94             sk_B))
% 18.76/18.94        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94            = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 18.76/18.94        | (r2_hidden @ 
% 18.76/18.94           (sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94            (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 18.76/18.94           (k1_tarski @ (k4_tarski @ sk_A @ sk_B))))),
% 18.76/18.94      inference('sup+', [status(thm)], ['81', '84'])).
% 18.76/18.94  thf('86', plain,
% 18.76/18.94      (((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 18.76/18.94         != (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.76/18.94  thf('87', plain,
% 18.76/18.94      ((((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94          (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94          = (k4_tarski @ 
% 18.76/18.94             (sk_E @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94              (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 18.76/18.94             sk_B))
% 18.76/18.94        | (r2_hidden @ 
% 18.76/18.94           (sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94            (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 18.76/18.94           (k1_tarski @ (k4_tarski @ sk_A @ sk_B))))),
% 18.76/18.94      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 18.76/18.94  thf('88', plain,
% 18.76/18.94      (![X0 : $i, X3 : $i]:
% 18.76/18.94         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['14'])).
% 18.76/18.94  thf('89', plain,
% 18.76/18.94      ((((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94          (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94          = (k4_tarski @ 
% 18.76/18.94             (sk_E @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94              (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 18.76/18.94             sk_B))
% 18.76/18.94        | ((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94            (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94            = (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('sup-', [status(thm)], ['87', '88'])).
% 18.76/18.94  thf('90', plain,
% 18.76/18.94      ((((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94          (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94            = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_B)))
% 18.76/18.94        | ((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94            (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94            = (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('sup+', [status(thm)], ['28', '89'])).
% 18.76/18.94  thf('91', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 18.76/18.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.76/18.94  thf('92', plain,
% 18.76/18.94      ((((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94          (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94            = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 18.76/18.94        | ((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94            (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94            = (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('demod', [status(thm)], ['90', '91'])).
% 18.76/18.94  thf('93', plain,
% 18.76/18.94      ((((k1_tarski @ (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94          = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 18.76/18.94        | ((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94            (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94            = (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('simplify', [status(thm)], ['92'])).
% 18.76/18.94  thf('94', plain,
% 18.76/18.94      (((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 18.76/18.94         != (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.76/18.94  thf('95', plain,
% 18.76/18.94      (((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ (k1_tarski @ sk_B) @ 
% 18.76/18.94         (k1_tarski @ sk_A)) = (k4_tarski @ sk_A @ sk_B))),
% 18.76/18.94      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 18.76/18.94  thf('96', plain,
% 18.76/18.94      (![X15 : $i, X16 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 18.76/18.94         (((X19) = (k2_zfmisc_1 @ X16 @ X15))
% 18.76/18.94          | ~ (zip_tseitin_0 @ X20 @ X21 @ (sk_D @ X19 @ X15 @ X16) @ X15 @ X16)
% 18.76/18.94          | ~ (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 18.76/18.94  thf('97', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (~ (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ sk_A @ sk_B) @ 
% 18.76/18.94             (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94          | ~ (r2_hidden @ 
% 18.76/18.94               (sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ 
% 18.76/18.94                (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 18.76/18.94               (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 18.76/18.94          | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94              = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 18.76/18.94      inference('sup-', [status(thm)], ['95', '96'])).
% 18.76/18.94  thf('98', plain,
% 18.76/18.94      (((sk_D @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)) @ (k1_tarski @ sk_B) @ 
% 18.76/18.94         (k1_tarski @ sk_A)) = (k4_tarski @ sk_A @ sk_B))),
% 18.76/18.94      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 18.76/18.94  thf('99', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 18.76/18.94      inference('simplify', [status(thm)], ['0'])).
% 18.76/18.94  thf('100', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         (~ (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ sk_A @ sk_B) @ 
% 18.76/18.94             (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 18.76/18.94          | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B))
% 18.76/18.94              = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 18.76/18.94      inference('demod', [status(thm)], ['97', '98', '99'])).
% 18.76/18.94  thf('101', plain,
% 18.76/18.94      (((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 18.76/18.94         != (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 18.76/18.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.76/18.94  thf('102', plain,
% 18.76/18.94      (![X0 : $i, X1 : $i]:
% 18.76/18.94         ~ (zip_tseitin_0 @ X1 @ X0 @ (k4_tarski @ sk_A @ sk_B) @ 
% 18.76/18.94            (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 18.76/18.94      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 18.76/18.94  thf('103', plain, ($false), inference('sup-', [status(thm)], ['6', '102'])).
% 18.76/18.94  
% 18.76/18.94  % SZS output end Refutation
% 18.76/18.94  
% 18.76/18.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
