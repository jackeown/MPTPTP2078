%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ywBjfQVr1L

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:26 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 324 expanded)
%              Number of leaves         :   27 ( 103 expanded)
%              Depth                    :   23
%              Number of atoms          :  958 (4157 expanded)
%              Number of equality atoms :  118 ( 528 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('0',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17 )
      | ( X13 = X14 )
      | ( X13 = X15 )
      | ( X13 = X16 )
      | ( X13 = X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( X30
       != ( k2_relat_1 @ X28 ) )
      | ( r2_hidden @ ( sk_D_1 @ X31 @ X28 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('5',plain,(
    ! [X28: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r2_hidden @ X31 @ ( k2_relat_1 @ X28 ) )
      | ( r2_hidden @ ( sk_D_1 @ X31 @ X28 ) @ ( k1_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X19 @ X20 @ X21 @ X22 )
      | ( X23
       != ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X19 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ sk_A @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('23',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( X30
       != ( k2_relat_1 @ X28 ) )
      | ( X31
        = ( k1_funct_1 @ X28 @ ( sk_D_1 @ X31 @ X28 ) ) )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('24',plain,(
    ! [X28: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r2_hidden @ X31 @ ( k2_relat_1 @ X28 ) )
      | ( X31
        = ( k1_funct_1 @ X28 @ ( sk_D_1 @ X31 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( sk_C @ X11 @ X10 )
       != X11 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X18 @ X23 )
      | ( X23
       != ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X18 @ ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    ! [X12: $i,X14: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X28: $i,X30: $i,X32: $i,X33: $i] :
      ( ( X30
       != ( k2_relat_1 @ X28 ) )
      | ( r2_hidden @ X32 @ X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X28 ) )
      | ( X32
       != ( k1_funct_1 @ X28 @ X33 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('50',plain,(
    ! [X28: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X33 ) @ ( k2_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('57',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17 )
      | ( X13 = X14 )
      | ( X13 = X15 )
      | ( X13 = X16 )
      | ( X13 = X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('60',plain,(
    ! [X26: $i] :
      ( ( ( k2_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( k1_funct_1 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['57','69'])).

thf('71',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('72',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['36','70','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ywBjfQVr1L
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.55/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.76  % Solved by: fo/fo7.sh
% 0.55/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.76  % done 328 iterations in 0.306s
% 0.55/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.76  % SZS output start Refutation
% 0.55/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.76  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.55/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.55/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.55/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.76  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.55/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.76  thf(t14_funct_1, conjecture,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.76       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.55/0.76         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.76    (~( ![A:$i,B:$i]:
% 0.55/0.76        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.76          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.55/0.76            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.55/0.76    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.55/0.76  thf('0', plain,
% 0.55/0.76      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(d2_enumset1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.55/0.76     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.55/0.76       ( ![F:$i]:
% 0.55/0.76         ( ( r2_hidden @ F @ E ) <=>
% 0.55/0.76           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.55/0.76                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_1, axiom,
% 0.55/0.76    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.55/0.76     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.55/0.76       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.55/0.76         ( ( F ) != ( D ) ) ) ))).
% 0.55/0.76  thf('1', plain,
% 0.55/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.55/0.76          | ((X13) = (X14))
% 0.55/0.76          | ((X13) = (X15))
% 0.55/0.76          | ((X13) = (X16))
% 0.55/0.76          | ((X13) = (X17)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.76  thf('2', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(l44_zfmisc_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.55/0.76          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.55/0.76  thf('3', plain,
% 0.55/0.76      (![X10 : $i, X11 : $i]:
% 0.55/0.76         (((X10) = (k1_xboole_0))
% 0.55/0.76          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.55/0.76          | ((X10) = (k1_tarski @ X11)))),
% 0.55/0.76      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.55/0.76  thf(d5_funct_1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.76       ( ![B:$i]:
% 0.55/0.76         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.55/0.76           ( ![C:$i]:
% 0.55/0.76             ( ( r2_hidden @ C @ B ) <=>
% 0.55/0.76               ( ?[D:$i]:
% 0.55/0.76                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.55/0.76                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.55/0.76  thf('4', plain,
% 0.55/0.76      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.55/0.76         (((X30) != (k2_relat_1 @ X28))
% 0.55/0.76          | (r2_hidden @ (sk_D_1 @ X31 @ X28) @ (k1_relat_1 @ X28))
% 0.55/0.76          | ~ (r2_hidden @ X31 @ X30)
% 0.55/0.76          | ~ (v1_funct_1 @ X28)
% 0.55/0.76          | ~ (v1_relat_1 @ X28))),
% 0.55/0.76      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.55/0.76  thf('5', plain,
% 0.55/0.76      (![X28 : $i, X31 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X28)
% 0.55/0.76          | ~ (v1_funct_1 @ X28)
% 0.55/0.76          | ~ (r2_hidden @ X31 @ (k2_relat_1 @ X28))
% 0.55/0.76          | (r2_hidden @ (sk_D_1 @ X31 @ X28) @ (k1_relat_1 @ X28)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['4'])).
% 0.55/0.76  thf('6', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 0.55/0.76          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.55/0.76          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.55/0.76             (k1_relat_1 @ X0))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['3', '5'])).
% 0.55/0.76  thf('7', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.55/0.76           (k1_tarski @ sk_A))
% 0.55/0.76          | ~ (v1_relat_1 @ sk_B)
% 0.55/0.76          | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['2', '6'])).
% 0.55/0.76  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('10', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.55/0.76           (k1_tarski @ sk_A))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.55/0.76      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.55/0.76  thf(t69_enumset1, axiom,
% 0.55/0.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.55/0.76  thf('11', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.76  thf(t70_enumset1, axiom,
% 0.55/0.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.55/0.76  thf('12', plain,
% 0.55/0.76      (![X1 : $i, X2 : $i]:
% 0.55/0.76         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.55/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.76  thf(t71_enumset1, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i]:
% 0.55/0.76     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.55/0.76  thf('13', plain,
% 0.55/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.76         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.55/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.55/0.76  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.55/0.76  thf(zf_stmt_3, axiom,
% 0.55/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.55/0.76     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.55/0.76       ( ![F:$i]:
% 0.55/0.76         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.55/0.76  thf('14', plain,
% 0.55/0.76      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X24 @ X23)
% 0.55/0.76          | ~ (zip_tseitin_0 @ X24 @ X19 @ X20 @ X21 @ X22)
% 0.55/0.76          | ((X23) != (k2_enumset1 @ X22 @ X21 @ X20 @ X19)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.76  thf('15', plain,
% 0.55/0.76      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.55/0.76         (~ (zip_tseitin_0 @ X24 @ X19 @ X20 @ X21 @ X22)
% 0.55/0.76          | ~ (r2_hidden @ X24 @ (k2_enumset1 @ X22 @ X21 @ X20 @ X19)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['14'])).
% 0.55/0.76  thf('16', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.55/0.76          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.55/0.76      inference('sup-', [status(thm)], ['13', '15'])).
% 0.55/0.76  thf('17', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.55/0.76          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.55/0.76      inference('sup-', [status(thm)], ['12', '16'])).
% 0.55/0.76  thf('18', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.55/0.76          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['11', '17'])).
% 0.55/0.76  thf('19', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ~ (zip_tseitin_0 @ 
% 0.55/0.76               (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ sk_A @ 
% 0.55/0.76               sk_A @ sk_A @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['10', '18'])).
% 0.55/0.76  thf('20', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.55/0.76          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.55/0.76          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.55/0.76          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['1', '19'])).
% 0.55/0.76  thf('21', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['20'])).
% 0.55/0.76  thf('22', plain,
% 0.55/0.76      (![X10 : $i, X11 : $i]:
% 0.55/0.76         (((X10) = (k1_xboole_0))
% 0.55/0.76          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.55/0.76          | ((X10) = (k1_tarski @ X11)))),
% 0.55/0.76      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.55/0.76  thf('23', plain,
% 0.55/0.76      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.55/0.76         (((X30) != (k2_relat_1 @ X28))
% 0.55/0.76          | ((X31) = (k1_funct_1 @ X28 @ (sk_D_1 @ X31 @ X28)))
% 0.55/0.76          | ~ (r2_hidden @ X31 @ X30)
% 0.55/0.76          | ~ (v1_funct_1 @ X28)
% 0.55/0.76          | ~ (v1_relat_1 @ X28))),
% 0.55/0.76      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.55/0.76  thf('24', plain,
% 0.55/0.76      (![X28 : $i, X31 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X28)
% 0.55/0.76          | ~ (v1_funct_1 @ X28)
% 0.55/0.76          | ~ (r2_hidden @ X31 @ (k2_relat_1 @ X28))
% 0.55/0.76          | ((X31) = (k1_funct_1 @ X28 @ (sk_D_1 @ X31 @ X28))))),
% 0.55/0.76      inference('simplify', [status(thm)], ['23'])).
% 0.55/0.76  thf('25', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 0.55/0.76          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.55/0.76          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.55/0.76              = (k1_funct_1 @ X0 @ 
% 0.55/0.76                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 0.55/0.76          | ~ (v1_funct_1 @ X0)
% 0.55/0.76          | ~ (v1_relat_1 @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['22', '24'])).
% 0.55/0.76  thf('26', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.55/0.76          | ~ (v1_relat_1 @ sk_B)
% 0.55/0.76          | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.55/0.76      inference('sup+', [status(thm)], ['21', '25'])).
% 0.55/0.76  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('29', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.55/0.76      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.55/0.76  thf('30', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['29'])).
% 0.55/0.76  thf('31', plain,
% 0.55/0.76      (![X10 : $i, X11 : $i]:
% 0.55/0.76         (((X10) = (k1_xboole_0))
% 0.55/0.76          | ((sk_C @ X11 @ X10) != (X11))
% 0.55/0.76          | ((X10) = (k1_tarski @ X11)))),
% 0.55/0.76      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.55/0.76  thf('32', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.55/0.76          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.55/0.76  thf('33', plain,
% 0.55/0.76      ((((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.55/0.76        | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['32'])).
% 0.55/0.76  thf('34', plain,
% 0.55/0.76      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('35', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.55/0.76      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.55/0.76  thf('36', plain,
% 0.55/0.76      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.55/0.76      inference('demod', [status(thm)], ['0', '35'])).
% 0.55/0.76  thf('37', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.55/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.76  thf('38', plain,
% 0.55/0.76      (![X1 : $i, X2 : $i]:
% 0.55/0.76         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.55/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.76  thf('39', plain,
% 0.55/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.76         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.55/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.55/0.76  thf('40', plain,
% 0.55/0.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.55/0.76          | (r2_hidden @ X18 @ X23)
% 0.55/0.76          | ((X23) != (k2_enumset1 @ X22 @ X21 @ X20 @ X19)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.76  thf('41', plain,
% 0.55/0.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.76         ((r2_hidden @ X18 @ (k2_enumset1 @ X22 @ X21 @ X20 @ X19))
% 0.55/0.76          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.55/0.76      inference('simplify', [status(thm)], ['40'])).
% 0.55/0.76  thf('42', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.76         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.55/0.76          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.55/0.76      inference('sup+', [status(thm)], ['39', '41'])).
% 0.55/0.76  thf('43', plain,
% 0.55/0.76      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.55/0.76         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.76  thf('44', plain,
% 0.55/0.76      (![X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.55/0.76         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12)),
% 0.55/0.76      inference('simplify', [status(thm)], ['43'])).
% 0.55/0.76  thf('45', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.76         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.55/0.76      inference('sup-', [status(thm)], ['42', '44'])).
% 0.55/0.76  thf('46', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.55/0.76      inference('sup+', [status(thm)], ['38', '45'])).
% 0.55/0.76  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.55/0.76      inference('sup+', [status(thm)], ['37', '46'])).
% 0.55/0.76  thf('48', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('49', plain,
% 0.55/0.76      (![X28 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 0.55/0.76         (((X30) != (k2_relat_1 @ X28))
% 0.55/0.76          | (r2_hidden @ X32 @ X30)
% 0.55/0.76          | ~ (r2_hidden @ X33 @ (k1_relat_1 @ X28))
% 0.55/0.76          | ((X32) != (k1_funct_1 @ X28 @ X33))
% 0.55/0.76          | ~ (v1_funct_1 @ X28)
% 0.55/0.76          | ~ (v1_relat_1 @ X28))),
% 0.55/0.76      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.55/0.76  thf('50', plain,
% 0.55/0.76      (![X28 : $i, X33 : $i]:
% 0.55/0.76         (~ (v1_relat_1 @ X28)
% 0.55/0.76          | ~ (v1_funct_1 @ X28)
% 0.55/0.76          | ~ (r2_hidden @ X33 @ (k1_relat_1 @ X28))
% 0.55/0.76          | (r2_hidden @ (k1_funct_1 @ X28 @ X33) @ (k2_relat_1 @ X28)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['49'])).
% 0.55/0.76  thf('51', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.55/0.76          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))
% 0.55/0.76          | ~ (v1_funct_1 @ sk_B)
% 0.55/0.76          | ~ (v1_relat_1 @ sk_B))),
% 0.55/0.76      inference('sup-', [status(thm)], ['48', '50'])).
% 0.55/0.76  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('54', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.55/0.76          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.55/0.76      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.55/0.76  thf('55', plain,
% 0.55/0.76      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.55/0.76      inference('sup-', [status(thm)], ['47', '54'])).
% 0.55/0.76  thf('56', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.55/0.76      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.55/0.76  thf('57', plain, ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ k1_xboole_0)),
% 0.55/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.55/0.76  thf('58', plain,
% 0.55/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.76         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.55/0.76          | ((X13) = (X14))
% 0.55/0.76          | ((X13) = (X15))
% 0.55/0.76          | ((X13) = (X16))
% 0.55/0.76          | ((X13) = (X17)))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.76  thf('59', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.55/0.76      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.55/0.76  thf(t65_relat_1, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( v1_relat_1 @ A ) =>
% 0.55/0.76       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.55/0.76         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.76  thf('60', plain,
% 0.55/0.76      (![X26 : $i]:
% 0.55/0.76         (((k2_relat_1 @ X26) != (k1_xboole_0))
% 0.55/0.76          | ((k1_relat_1 @ X26) = (k1_xboole_0))
% 0.55/0.76          | ~ (v1_relat_1 @ X26))),
% 0.55/0.76      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.55/0.76  thf('61', plain,
% 0.55/0.76      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.76        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.76        | ((k1_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.55/0.76      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.76  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('63', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('64', plain,
% 0.55/0.76      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.55/0.76      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.55/0.76  thf('65', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.55/0.76      inference('simplify', [status(thm)], ['64'])).
% 0.55/0.76  thf('66', plain,
% 0.55/0.76      (![X0 : $i, X1 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.55/0.76          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['11', '17'])).
% 0.55/0.76  thf('67', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.55/0.76          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.55/0.76  thf('68', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (((X0) = (sk_A))
% 0.55/0.76          | ((X0) = (sk_A))
% 0.55/0.76          | ((X0) = (sk_A))
% 0.55/0.76          | ((X0) = (sk_A))
% 0.55/0.76          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.55/0.76      inference('sup-', [status(thm)], ['58', '67'])).
% 0.55/0.76  thf('69', plain,
% 0.55/0.76      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A)))),
% 0.55/0.76      inference('simplify', [status(thm)], ['68'])).
% 0.55/0.76  thf('70', plain, (((k1_funct_1 @ sk_B @ sk_A) = (sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['57', '69'])).
% 0.55/0.76  thf('71', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.55/0.76      inference('simplify', [status(thm)], ['64'])).
% 0.55/0.76  thf('72', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.55/0.76      inference('demod', [status(thm)], ['36', '70', '71'])).
% 0.55/0.76  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.55/0.76  
% 0.55/0.76  % SZS output end Refutation
% 0.55/0.76  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
