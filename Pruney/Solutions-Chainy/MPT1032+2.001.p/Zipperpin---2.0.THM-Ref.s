%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MNHEUXtYi9

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:04 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 124 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :  931 (1580 expanded)
%              Number of equality atoms :   24 (  55 expanded)
%              Maximal formula depth    :   17 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_partfun1_type,type,(
    k4_partfun1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t141_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_funct_2 @ A @ B ) @ ( k4_partfun1 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k1_funct_2 @ A @ B ) @ ( k4_partfun1 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t141_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_funct_2 @ sk_A @ sk_B ) @ ( k4_partfun1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ( X16
       != ( k1_funct_2 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_funct_2 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9 = X7 )
      | ~ ( zip_tseitin_0 @ X7 @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) )
        = ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X7 @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( v1_funct_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) )
        = ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X7 @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( v1_relat_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( v1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) )
        = ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ X7 )
        = X10 )
      | ~ ( zip_tseitin_0 @ X7 @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( k1_relat_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( ( k1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) )
        = ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( zip_tseitin_0 @ X7 @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(d5_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_partfun1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( r1_tarski @ ( k1_relat_1 @ E ) @ A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( r1_tarski @ ( k1_relat_1 @ E ) @ A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X20 @ X22 @ X21 @ X24 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X22 != X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X24 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 )
      | ( zip_tseitin_1 @ X20 @ X20 @ X21 @ X24 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 )
      | ~ ( v1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_funct_2 @ X0 @ X2 ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) )
      | ( zip_tseitin_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) @ X2 @ X1 )
      | ( r1_tarski @ ( k1_funct_2 @ X0 @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) @ X2 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) )
      | ( r1_tarski @ ( k1_funct_2 @ X0 @ X2 ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X2 ) @ X1 )
      | ( zip_tseitin_1 @ ( sk_C @ X1 @ ( k1_funct_2 @ X0 @ X2 ) ) @ ( sk_C @ X1 @ ( k1_funct_2 @ X0 @ X2 ) ) @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','40'])).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_partfun1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_1 @ E @ D @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_1 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X26 @ X29 )
      | ( X29
       != ( k4_partfun1 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('43',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X26 @ ( k4_partfun1 @ X28 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ ( k4_partfun1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ ( k4_partfun1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ ( k4_partfun1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ ( k4_partfun1 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MNHEUXtYi9
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.35/1.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.60  % Solved by: fo/fo7.sh
% 1.35/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.60  % done 633 iterations in 1.144s
% 1.35/1.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.60  % SZS output start Refutation
% 1.35/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 1.35/1.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.35/1.60  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.35/1.60  thf(k4_partfun1_type, type, k4_partfun1: $i > $i > $i).
% 1.35/1.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.35/1.60  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.35/1.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.60  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 1.35/1.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.35/1.60  thf(t141_funct_2, conjecture,
% 1.35/1.60    (![A:$i,B:$i]:
% 1.35/1.60     ( r1_tarski @ ( k1_funct_2 @ A @ B ) @ ( k4_partfun1 @ A @ B ) ))).
% 1.35/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.60    (~( ![A:$i,B:$i]:
% 1.35/1.60        ( r1_tarski @ ( k1_funct_2 @ A @ B ) @ ( k4_partfun1 @ A @ B ) ) )),
% 1.35/1.60    inference('cnf.neg', [status(esa)], [t141_funct_2])).
% 1.35/1.60  thf('0', plain,
% 1.35/1.60      (~ (r1_tarski @ (k1_funct_2 @ sk_A @ sk_B) @ (k4_partfun1 @ sk_A @ sk_B))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.60  thf(d10_xboole_0, axiom,
% 1.35/1.60    (![A:$i,B:$i]:
% 1.35/1.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.35/1.60  thf('1', plain,
% 1.35/1.60      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.35/1.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.60  thf('2', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.35/1.60      inference('simplify', [status(thm)], ['1'])).
% 1.35/1.60  thf(d3_tarski, axiom,
% 1.35/1.60    (![A:$i,B:$i]:
% 1.35/1.60     ( ( r1_tarski @ A @ B ) <=>
% 1.35/1.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.35/1.60  thf('3', plain,
% 1.35/1.60      (![X1 : $i, X3 : $i]:
% 1.35/1.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.35/1.60      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.60  thf(d2_funct_2, axiom,
% 1.35/1.60    (![A:$i,B:$i,C:$i]:
% 1.35/1.60     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.35/1.60       ( ![D:$i]:
% 1.35/1.60         ( ( r2_hidden @ D @ C ) <=>
% 1.35/1.60           ( ?[E:$i]:
% 1.35/1.60             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 1.35/1.60               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 1.35/1.60               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 1.35/1.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.35/1.60  thf(zf_stmt_2, axiom,
% 1.35/1.60    (![E:$i,D:$i,B:$i,A:$i]:
% 1.35/1.60     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 1.35/1.60       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 1.35/1.60         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 1.35/1.60         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 1.35/1.60  thf(zf_stmt_3, axiom,
% 1.35/1.60    (![A:$i,B:$i,C:$i]:
% 1.35/1.60     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.35/1.60       ( ![D:$i]:
% 1.35/1.60         ( ( r2_hidden @ D @ C ) <=>
% 1.35/1.60           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 1.35/1.60  thf('4', plain,
% 1.35/1.60      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.35/1.60         (~ (r2_hidden @ X17 @ X16)
% 1.35/1.60          | (zip_tseitin_0 @ (sk_E_1 @ X17 @ X14 @ X15) @ X17 @ X14 @ X15)
% 1.35/1.60          | ((X16) != (k1_funct_2 @ X15 @ X14)))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.35/1.60  thf('5', plain,
% 1.35/1.60      (![X14 : $i, X15 : $i, X17 : $i]:
% 1.35/1.60         ((zip_tseitin_0 @ (sk_E_1 @ X17 @ X14 @ X15) @ X17 @ X14 @ X15)
% 1.35/1.60          | ~ (r2_hidden @ X17 @ (k1_funct_2 @ X15 @ X14)))),
% 1.35/1.60      inference('simplify', [status(thm)], ['4'])).
% 1.35/1.60  thf('6', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (zip_tseitin_0 @ 
% 1.35/1.60             (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.35/1.60             (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1))),
% 1.35/1.60      inference('sup-', [status(thm)], ['3', '5'])).
% 1.35/1.60  thf('7', plain,
% 1.35/1.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.35/1.60         (((X9) = (X7)) | ~ (zip_tseitin_0 @ X7 @ X9 @ X8 @ X10))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.35/1.60  thf('8', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | ((sk_C @ X2 @ (k1_funct_2 @ X0 @ X1))
% 1.35/1.60              = (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ X1 @ X0)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.60  thf('9', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (zip_tseitin_0 @ 
% 1.35/1.60             (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.35/1.60             (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1))),
% 1.35/1.60      inference('sup-', [status(thm)], ['3', '5'])).
% 1.35/1.60  thf('10', plain,
% 1.35/1.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.35/1.60         ((v1_funct_1 @ X7) | ~ (zip_tseitin_0 @ X7 @ X9 @ X8 @ X10))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.35/1.60  thf('11', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | (v1_funct_1 @ 
% 1.35/1.60             (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ X1 @ X0)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['9', '10'])).
% 1.35/1.60  thf('12', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((v1_funct_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)))
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2))),
% 1.35/1.60      inference('sup+', [status(thm)], ['8', '11'])).
% 1.35/1.60  thf('13', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (v1_funct_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0))))),
% 1.35/1.60      inference('simplify', [status(thm)], ['12'])).
% 1.35/1.60  thf('14', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | ((sk_C @ X2 @ (k1_funct_2 @ X0 @ X1))
% 1.35/1.60              = (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ X1 @ X0)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.60  thf('15', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (zip_tseitin_0 @ 
% 1.35/1.60             (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.35/1.60             (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1))),
% 1.35/1.60      inference('sup-', [status(thm)], ['3', '5'])).
% 1.35/1.60  thf('16', plain,
% 1.35/1.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.35/1.60         ((v1_relat_1 @ X7) | ~ (zip_tseitin_0 @ X7 @ X9 @ X8 @ X10))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.35/1.60  thf('17', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | (v1_relat_1 @ 
% 1.35/1.60             (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ X1 @ X0)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['15', '16'])).
% 1.35/1.60  thf('18', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((v1_relat_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)))
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2))),
% 1.35/1.60      inference('sup+', [status(thm)], ['14', '17'])).
% 1.35/1.60  thf('19', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (v1_relat_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0))))),
% 1.35/1.60      inference('simplify', [status(thm)], ['18'])).
% 1.35/1.60  thf('20', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | ((sk_C @ X2 @ (k1_funct_2 @ X0 @ X1))
% 1.35/1.60              = (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ X1 @ X0)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.60  thf('21', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (zip_tseitin_0 @ 
% 1.35/1.60             (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.35/1.60             (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1))),
% 1.35/1.60      inference('sup-', [status(thm)], ['3', '5'])).
% 1.35/1.60  thf('22', plain,
% 1.35/1.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.35/1.60         (((k1_relat_1 @ X7) = (X10)) | ~ (zip_tseitin_0 @ X7 @ X9 @ X8 @ X10))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.35/1.60  thf('23', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | ((k1_relat_1 @ 
% 1.35/1.60              (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ X1 @ X0)) = (
% 1.35/1.60              X0)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['21', '22'])).
% 1.35/1.60  thf('24', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         (((k1_relat_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0))) = (X1))
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2))),
% 1.35/1.60      inference('sup+', [status(thm)], ['20', '23'])).
% 1.35/1.60  thf('25', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | ((k1_relat_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0))) = (X1)))),
% 1.35/1.60      inference('simplify', [status(thm)], ['24'])).
% 1.35/1.60  thf('26', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | ((sk_C @ X2 @ (k1_funct_2 @ X0 @ X1))
% 1.35/1.60              = (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ X1 @ X0)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.60  thf('27', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (zip_tseitin_0 @ 
% 1.35/1.60             (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.35/1.60             (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X1))),
% 1.35/1.60      inference('sup-', [status(thm)], ['3', '5'])).
% 1.35/1.60  thf('28', plain,
% 1.35/1.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.35/1.60         ((r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 1.35/1.60          | ~ (zip_tseitin_0 @ X7 @ X9 @ X8 @ X10))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.35/1.60  thf('29', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | (r1_tarski @ 
% 1.35/1.60             (k2_relat_1 @ 
% 1.35/1.60              (sk_E_1 @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ X1 @ X0)) @ 
% 1.35/1.60             X1))),
% 1.35/1.60      inference('sup-', [status(thm)], ['27', '28'])).
% 1.35/1.60  thf('30', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k2_relat_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0))) @ X0)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2))),
% 1.35/1.60      inference('sup+', [status(thm)], ['26', '29'])).
% 1.35/1.60  thf('31', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (r1_tarski @ (k2_relat_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0))) @ 
% 1.35/1.60             X0))),
% 1.35/1.60      inference('simplify', [status(thm)], ['30'])).
% 1.35/1.60  thf(d5_partfun1, axiom,
% 1.35/1.60    (![A:$i,B:$i,C:$i]:
% 1.35/1.60     ( ( ( C ) = ( k4_partfun1 @ A @ B ) ) <=>
% 1.35/1.60       ( ![D:$i]:
% 1.35/1.60         ( ( r2_hidden @ D @ C ) <=>
% 1.35/1.60           ( ?[E:$i]:
% 1.35/1.60             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 1.35/1.60               ( r1_tarski @ ( k1_relat_1 @ E ) @ A ) & 
% 1.35/1.60               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 1.35/1.60  thf(zf_stmt_4, axiom,
% 1.35/1.60    (![E:$i,D:$i,B:$i,A:$i]:
% 1.35/1.60     ( ( zip_tseitin_1 @ E @ D @ B @ A ) <=>
% 1.35/1.60       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 1.35/1.60         ( r1_tarski @ ( k1_relat_1 @ E ) @ A ) & ( ( D ) = ( E ) ) & 
% 1.35/1.60         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 1.35/1.60  thf('32', plain,
% 1.35/1.60      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 1.35/1.60         ((zip_tseitin_1 @ X20 @ X22 @ X21 @ X24)
% 1.35/1.60          | ~ (v1_relat_1 @ X20)
% 1.35/1.60          | ~ (v1_funct_1 @ X20)
% 1.35/1.60          | ((X22) != (X20))
% 1.35/1.60          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ X24)
% 1.35/1.60          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X21))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.35/1.60  thf('33', plain,
% 1.35/1.60      (![X20 : $i, X21 : $i, X24 : $i]:
% 1.35/1.60         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 1.35/1.60          | ~ (r1_tarski @ (k1_relat_1 @ X20) @ X24)
% 1.35/1.60          | ~ (v1_funct_1 @ X20)
% 1.35/1.60          | ~ (v1_relat_1 @ X20)
% 1.35/1.60          | (zip_tseitin_1 @ X20 @ X20 @ X21 @ X24))),
% 1.35/1.60      inference('simplify', [status(thm)], ['32'])).
% 1.35/1.60  thf('34', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (zip_tseitin_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ 
% 1.35/1.60             (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X3)
% 1.35/1.60          | ~ (v1_relat_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)))
% 1.35/1.60          | ~ (v1_funct_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)))
% 1.35/1.60          | ~ (r1_tarski @ 
% 1.35/1.60               (k1_relat_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0))) @ X3))),
% 1.35/1.60      inference('sup-', [status(thm)], ['31', '33'])).
% 1.35/1.60  thf('35', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.60         (~ (r1_tarski @ X0 @ X1)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X0 @ X2) @ X3)
% 1.35/1.60          | ~ (v1_funct_1 @ (sk_C @ X3 @ (k1_funct_2 @ X0 @ X2)))
% 1.35/1.60          | ~ (v1_relat_1 @ (sk_C @ X3 @ (k1_funct_2 @ X0 @ X2)))
% 1.35/1.60          | (zip_tseitin_1 @ (sk_C @ X3 @ (k1_funct_2 @ X0 @ X2)) @ 
% 1.35/1.60             (sk_C @ X3 @ (k1_funct_2 @ X0 @ X2)) @ X2 @ X1)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X0 @ X2) @ X3))),
% 1.35/1.60      inference('sup-', [status(thm)], ['25', '34'])).
% 1.35/1.60  thf('36', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.60         ((zip_tseitin_1 @ (sk_C @ X3 @ (k1_funct_2 @ X0 @ X2)) @ 
% 1.35/1.60           (sk_C @ X3 @ (k1_funct_2 @ X0 @ X2)) @ X2 @ X1)
% 1.35/1.60          | ~ (v1_relat_1 @ (sk_C @ X3 @ (k1_funct_2 @ X0 @ X2)))
% 1.35/1.60          | ~ (v1_funct_1 @ (sk_C @ X3 @ (k1_funct_2 @ X0 @ X2)))
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X0 @ X2) @ X3)
% 1.35/1.60          | ~ (r1_tarski @ X0 @ X1))),
% 1.35/1.60      inference('simplify', [status(thm)], ['35'])).
% 1.35/1.60  thf('37', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | ~ (r1_tarski @ X1 @ X3)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | ~ (v1_funct_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)))
% 1.35/1.60          | (zip_tseitin_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ 
% 1.35/1.60             (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X3))),
% 1.35/1.60      inference('sup-', [status(thm)], ['19', '36'])).
% 1.35/1.60  thf('38', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.60         ((zip_tseitin_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ 
% 1.35/1.60           (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X3)
% 1.35/1.60          | ~ (v1_funct_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)))
% 1.35/1.60          | ~ (r1_tarski @ X1 @ X3)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2))),
% 1.35/1.60      inference('simplify', [status(thm)], ['37'])).
% 1.35/1.60  thf('39', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2)
% 1.35/1.60          | ~ (r1_tarski @ X1 @ X3)
% 1.35/1.60          | (zip_tseitin_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ 
% 1.35/1.60             (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X3))),
% 1.35/1.60      inference('sup-', [status(thm)], ['13', '38'])).
% 1.35/1.60  thf('40', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.60         ((zip_tseitin_1 @ (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ 
% 1.35/1.60           (sk_C @ X2 @ (k1_funct_2 @ X1 @ X0)) @ X0 @ X3)
% 1.35/1.60          | ~ (r1_tarski @ X1 @ X3)
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ X2))),
% 1.35/1.60      inference('simplify', [status(thm)], ['39'])).
% 1.35/1.60  thf('41', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X2) @ X1)
% 1.35/1.60          | (zip_tseitin_1 @ (sk_C @ X1 @ (k1_funct_2 @ X0 @ X2)) @ 
% 1.35/1.60             (sk_C @ X1 @ (k1_funct_2 @ X0 @ X2)) @ X2 @ X0))),
% 1.35/1.60      inference('sup-', [status(thm)], ['2', '40'])).
% 1.35/1.60  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 1.35/1.60  thf(zf_stmt_6, axiom,
% 1.35/1.60    (![A:$i,B:$i,C:$i]:
% 1.35/1.60     ( ( ( C ) = ( k4_partfun1 @ A @ B ) ) <=>
% 1.35/1.60       ( ![D:$i]:
% 1.35/1.60         ( ( r2_hidden @ D @ C ) <=>
% 1.35/1.60           ( ?[E:$i]: ( zip_tseitin_1 @ E @ D @ B @ A ) ) ) ) ))).
% 1.35/1.60  thf('42', plain,
% 1.35/1.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.35/1.60         (~ (zip_tseitin_1 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.60          | (r2_hidden @ X26 @ X29)
% 1.35/1.60          | ((X29) != (k4_partfun1 @ X28 @ X27)))),
% 1.35/1.60      inference('cnf', [status(esa)], [zf_stmt_6])).
% 1.35/1.60  thf('43', plain,
% 1.35/1.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.60         ((r2_hidden @ X26 @ (k4_partfun1 @ X28 @ X27))
% 1.35/1.60          | ~ (zip_tseitin_1 @ X25 @ X26 @ X27 @ X28))),
% 1.35/1.60      inference('simplify', [status(thm)], ['42'])).
% 1.35/1.60  thf('44', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X0 @ X1) @ X2)
% 1.35/1.60          | (r2_hidden @ (sk_C @ X2 @ (k1_funct_2 @ X0 @ X1)) @ 
% 1.35/1.60             (k4_partfun1 @ X0 @ X1)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['41', '43'])).
% 1.35/1.60  thf('45', plain,
% 1.35/1.60      (![X1 : $i, X3 : $i]:
% 1.35/1.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.35/1.60      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.60  thf('46', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i]:
% 1.35/1.60         ((r1_tarski @ (k1_funct_2 @ X1 @ X0) @ (k4_partfun1 @ X1 @ X0))
% 1.35/1.60          | (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ (k4_partfun1 @ X1 @ X0)))),
% 1.35/1.60      inference('sup-', [status(thm)], ['44', '45'])).
% 1.35/1.60  thf('47', plain,
% 1.35/1.60      (![X0 : $i, X1 : $i]:
% 1.35/1.60         (r1_tarski @ (k1_funct_2 @ X1 @ X0) @ (k4_partfun1 @ X1 @ X0))),
% 1.35/1.60      inference('simplify', [status(thm)], ['46'])).
% 1.35/1.60  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 1.35/1.60  
% 1.35/1.60  % SZS output end Refutation
% 1.35/1.60  
% 1.35/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
