%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LQJbGDsWfR

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:55 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 127 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  938 (1605 expanded)
%              Number of equality atoms :   22 (  53 expanded)
%              Maximal formula depth    :   17 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_partfun1_type,type,(
    k4_partfun1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X16 ) ) ),
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

thf('5',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X14 ) ) ),
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

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X7 @ X8 ) @ X10 @ X7 @ X8 )
      | ( X9
       != ( k1_funct_2 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X7 @ X8 ) @ X10 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_funct_2 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2 = X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) )
        = ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( v1_funct_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) )
        = ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( v1_relat_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( v1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) )
        = ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = X3 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( k1_relat_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( ( k1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) )
        = ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

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

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X17 @ X19 @ X18 @ X21 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X19 != X17 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('35',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X21 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ( zip_tseitin_1 @ X17 @ X17 @ X18 @ X21 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 )
      | ~ ( v1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_funct_2 @ X0 @ X2 ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) )
      | ( zip_tseitin_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) @ X2 @ X1 )
      | ( r1_tarski @ ( k1_funct_2 @ X0 @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) @ X2 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X3 @ ( k1_funct_2 @ X0 @ X2 ) ) )
      | ( r1_tarski @ ( k1_funct_2 @ X0 @ X2 ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_funct_2 @ X1 @ X0 ) ) @ X0 @ X3 )
      | ~ ( r1_tarski @ X1 @ X3 )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X2 ) @ X1 )
      | ( zip_tseitin_1 @ ( sk_C @ X1 @ ( k1_funct_2 @ X0 @ X2 ) ) @ ( sk_C @ X1 @ ( k1_funct_2 @ X0 @ X2 ) ) @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','42'])).

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

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_1 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X23 @ X26 )
      | ( X26
       != ( k4_partfun1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ ( k4_partfun1 @ X25 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_funct_2 @ X0 @ X1 ) ) @ ( k4_partfun1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X16 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X14 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ ( k4_partfun1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ ( k4_partfun1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_funct_2 @ X1 @ X0 ) @ ( k4_partfun1 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).


%------------------------------------------------------------------------------
