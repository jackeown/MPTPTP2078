%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jSlqFSxCde

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:26 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  254 ( 628 expanded)
%              Number of leaves         :   35 ( 198 expanded)
%              Depth                    :   42
%              Number of atoms          : 2677 (7367 expanded)
%              Number of equality atoms :  294 ( 764 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      | ( X27 = X28 )
      | ( X27 = X29 )
      | ( X27 = X30 )
      | ( X27 = X31 )
      | ( X27 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      | ( X27 = X28 )
      | ( X27 = X29 )
      | ( X27 = X30 )
      | ( X27 = X31 )
      | ( X27 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('3',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X43 @ X44 ) @ X43 )
      | ( r2_hidden @ ( sk_D @ X43 @ X44 ) @ ( k1_relat_1 @ X44 ) )
      | ( X43
        = ( k2_relat_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ X39 )
      | ~ ( zip_tseitin_0 @ X40 @ X34 @ X35 @ X36 @ X37 @ X38 )
      | ( X39
       != ( k3_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X34 @ X35 @ X36 @ X37 @ X38 )
      | ~ ( r2_hidden @ X40 @ ( k3_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X0 @ sk_B_1 ) @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_D @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X43 @ X44 ) @ X43 )
      | ( ( sk_C_1 @ X43 @ X44 )
        = ( k1_funct_1 @ X44 @ ( sk_D @ X43 @ X44 ) ) )
      | ( X43
        = ( k2_relat_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ X0 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ X0 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ sk_B_1 )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ sk_B_1 )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C_1 @ X0 @ sk_B_1 )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X42: $i] :
      ( ( ( k2_relat_1 @ X42 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X42 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_1 @ X0 @ sk_B_1 )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_1 @ X0 @ sk_B_1 )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_C_1 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_C_1 @ k1_xboole_0 @ sk_B_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      | ( X27 = X28 )
      | ( X27 = X29 )
      | ( X27 = X30 )
      | ( X27 = X31 )
      | ( X27 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k2_tarski @ X1 @ X0 ) ) @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 @ X0 @ X0 )
      | ( v1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X25 @ X24 ) @ X24 )
      | ( X24
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      | ( X27 = X28 )
      | ( X27 = X29 )
      | ( X27 = X30 )
      | ( X27 = X31 )
      | ( X27 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('68',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( X46
       != ( k2_relat_1 @ X44 ) )
      | ( r2_hidden @ ( sk_D_1 @ X47 @ X44 ) @ ( k1_relat_1 @ X44 ) )
      | ~ ( r2_hidden @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('70',plain,(
    ! [X44: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X47 @ ( k2_relat_1 @ X44 ) )
      | ( r2_hidden @ ( sk_D_1 @ X47 @ X44 ) @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('80',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B_1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','83'])).

thf('85',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X42: $i] :
      ( ( ( k2_relat_1 @ X42 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X42 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      | ( X27 = X28 )
      | ( X27 = X29 )
      | ( X27 = X30 )
      | ( X27 = X31 )
      | ( X27 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('96',plain,(
    ! [X44: $i,X46: $i,X48: $i,X49: $i] :
      ( ( X46
       != ( k2_relat_1 @ X44 ) )
      | ( r2_hidden @ X48 @ X46 )
      | ~ ( r2_hidden @ X49 @ ( k1_relat_1 @ X44 ) )
      | ( X48
       != ( k1_funct_1 @ X44 @ X49 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('97',plain,(
    ! [X44: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X49 @ ( k1_relat_1 @ X44 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X44 @ X49 ) @ ( k2_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('100',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,(
    ! [X44: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X47 @ ( k2_relat_1 @ X44 ) )
      | ( r2_hidden @ ( sk_D_1 @ X47 @ X44 ) @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('106',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('107',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('108',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ) @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 )
      = sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 )
      = sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 )
      = sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 )
      = sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['92','112'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','82'])).

thf('116',plain,(
    ! [X42: $i] :
      ( ( ( k2_relat_1 @ X42 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X42 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['121','123'])).

thf('125',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['114','124'])).

thf('126',plain,
    ( ( ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_B_1 ) @ sk_B_1 )
      = sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','125'])).

thf('127',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_B_1 ) @ sk_B_1 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ X0 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ X0 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('130',plain,(
    ! [X44: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X49 @ ( k1_relat_1 @ X44 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X44 @ X49 ) @ ( k2_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X44: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X47 @ ( k2_relat_1 @ X44 ) )
      | ( r2_hidden @ ( sk_D_1 @ X47 @ X44 ) @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['127','137'])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('140',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('141',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('142',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('143',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('145',plain,(
    ! [X42: $i] :
      ( ( ( k1_relat_1 @ X42 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X42 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('146',plain,
    ( ( ( k1_tarski @ sk_A )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('148',plain,
    ( ( ( k1_tarski @ sk_A )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['143','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('151',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X44: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X47 @ ( k2_relat_1 @ X44 ) )
      | ( r2_hidden @ ( sk_D_1 @ X47 @ X44 ) @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('153',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('155',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('156',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('157',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('159',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','159'])).

thf('161',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('163',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('164',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['161','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('168',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('170',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('171',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('172',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('173',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      | ( r2_hidden @ X33 @ X39 )
      | ( X39
       != ( k3_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('174',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X33 @ ( k3_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 ) )
      | ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['172','174'])).

thf('176',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X27 != X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X26: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X30 @ X31 @ X26 ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['175','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','182'])).

thf('184',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['168','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ X0 ) @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('186',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('188',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      | ( X27 = X28 )
      | ( X27 = X29 )
      | ( X27 = X30 )
      | ( X27 = X31 )
      | ( X27 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('191',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X25 @ X24 ) @ X24 )
      | ( X24
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('192',plain,(
    ! [X44: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X47 @ ( k2_relat_1 @ X44 ) )
      | ( r2_hidden @ ( sk_D_1 @ X47 @ X44 ) @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['190','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('196',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 ) @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
        = sk_A )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_B_1 )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X25 @ X24 ) @ X24 )
      | ( X24
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('203',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( X46
       != ( k2_relat_1 @ X44 ) )
      | ( X47
        = ( k1_funct_1 @ X44 @ ( sk_D_1 @ X47 @ X44 ) ) )
      | ~ ( r2_hidden @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('204',plain,(
    ! [X44: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( r2_hidden @ X47 @ ( k2_relat_1 @ X44 ) )
      | ( X47
        = ( k1_funct_1 @ X44 @ ( sk_D_1 @ X47 @ X44 ) ) ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['202','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['201','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('208',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( ( sk_C @ X25 @ X24 )
       != X25 )
      | ( X24
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('215',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('217',plain,(
    $false ),
    inference(demod,[status(thm)],['188','215','216'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jSlqFSxCde
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.40/2.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.40/2.63  % Solved by: fo/fo7.sh
% 2.40/2.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.40/2.63  % done 1452 iterations in 2.168s
% 2.40/2.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.40/2.63  % SZS output start Refutation
% 2.40/2.63  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.40/2.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.40/2.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.40/2.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.40/2.63  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 2.40/2.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.40/2.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.40/2.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.40/2.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.40/2.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.40/2.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 2.40/2.63  thf(sk_A_type, type, sk_A: $i).
% 2.40/2.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.40/2.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.40/2.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.40/2.63  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.40/2.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.40/2.63  thf(sk_B_type, type, sk_B: $i > $i).
% 2.40/2.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.40/2.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.40/2.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.40/2.63  thf(d3_enumset1, axiom,
% 2.40/2.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.40/2.63     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 2.40/2.63       ( ![G:$i]:
% 2.40/2.63         ( ( r2_hidden @ G @ F ) <=>
% 2.40/2.63           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 2.40/2.63                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 2.40/2.63  thf(zf_stmt_0, axiom,
% 2.40/2.63    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 2.40/2.63     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 2.40/2.63       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 2.40/2.63         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 2.40/2.63  thf('0', plain,
% 2.40/2.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.63         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 2.40/2.63          | ((X27) = (X28))
% 2.40/2.63          | ((X27) = (X29))
% 2.40/2.63          | ((X27) = (X30))
% 2.40/2.63          | ((X27) = (X31))
% 2.40/2.63          | ((X27) = (X32)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.63  thf('1', plain,
% 2.40/2.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.63         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 2.40/2.63          | ((X27) = (X28))
% 2.40/2.63          | ((X27) = (X29))
% 2.40/2.63          | ((X27) = (X30))
% 2.40/2.63          | ((X27) = (X31))
% 2.40/2.63          | ((X27) = (X32)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.63  thf(t14_funct_1, conjecture,
% 2.40/2.63    (![A:$i,B:$i]:
% 2.40/2.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.40/2.63       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 2.40/2.63         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 2.40/2.63  thf(zf_stmt_1, negated_conjecture,
% 2.40/2.63    (~( ![A:$i,B:$i]:
% 2.40/2.63        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.40/2.63          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 2.40/2.63            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 2.40/2.63    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 2.40/2.63  thf('2', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf(d5_funct_1, axiom,
% 2.40/2.63    (![A:$i]:
% 2.40/2.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.40/2.63       ( ![B:$i]:
% 2.40/2.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.40/2.63           ( ![C:$i]:
% 2.40/2.63             ( ( r2_hidden @ C @ B ) <=>
% 2.40/2.63               ( ?[D:$i]:
% 2.40/2.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 2.40/2.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 2.40/2.63  thf('3', plain,
% 2.40/2.63      (![X43 : $i, X44 : $i]:
% 2.40/2.63         ((r2_hidden @ (sk_C_1 @ X43 @ X44) @ X43)
% 2.40/2.63          | (r2_hidden @ (sk_D @ X43 @ X44) @ (k1_relat_1 @ X44))
% 2.40/2.63          | ((X43) = (k2_relat_1 @ X44))
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (v1_relat_1 @ X44))),
% 2.40/2.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.40/2.63  thf(d1_xboole_0, axiom,
% 2.40/2.63    (![A:$i]:
% 2.40/2.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.40/2.63  thf('4', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('5', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X1)
% 2.40/2.63          | ~ (v1_funct_1 @ X1)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ X1))
% 2.40/2.63          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k1_relat_1 @ X1))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['3', '4'])).
% 2.40/2.63  thf('6', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((r2_hidden @ (sk_D @ X0 @ sk_B_1) @ (k1_tarski @ sk_A))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63          | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63          | ~ (v1_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup+', [status(thm)], ['2', '5'])).
% 2.40/2.63  thf('7', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('8', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('9', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((r2_hidden @ (sk_D @ X0 @ sk_B_1) @ (k1_tarski @ sk_A))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('demod', [status(thm)], ['6', '7', '8'])).
% 2.40/2.63  thf(t69_enumset1, axiom,
% 2.40/2.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.40/2.63  thf('10', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 2.40/2.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.40/2.63  thf(t70_enumset1, axiom,
% 2.40/2.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.40/2.63  thf('11', plain,
% 2.40/2.63      (![X4 : $i, X5 : $i]:
% 2.40/2.63         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 2.40/2.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.40/2.63  thf(t71_enumset1, axiom,
% 2.40/2.63    (![A:$i,B:$i,C:$i]:
% 2.40/2.63     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.40/2.63  thf('12', plain,
% 2.40/2.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.40/2.63         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 2.40/2.63      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.40/2.63  thf(t72_enumset1, axiom,
% 2.40/2.63    (![A:$i,B:$i,C:$i,D:$i]:
% 2.40/2.63     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.40/2.63  thf('13', plain,
% 2.40/2.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.40/2.63         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 2.40/2.63           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 2.40/2.63      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.40/2.63  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 2.40/2.63  thf(zf_stmt_3, axiom,
% 2.40/2.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.40/2.63     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 2.40/2.63       ( ![G:$i]:
% 2.40/2.63         ( ( r2_hidden @ G @ F ) <=>
% 2.40/2.63           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 2.40/2.63  thf('14', plain,
% 2.40/2.63      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X40 @ X39)
% 2.40/2.63          | ~ (zip_tseitin_0 @ X40 @ X34 @ X35 @ X36 @ X37 @ X38)
% 2.40/2.63          | ((X39) != (k3_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.40/2.63  thf('15', plain,
% 2.40/2.63      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 2.40/2.63         (~ (zip_tseitin_0 @ X40 @ X34 @ X35 @ X36 @ X37 @ X38)
% 2.40/2.63          | ~ (r2_hidden @ X40 @ (k3_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['14'])).
% 2.40/2.63  thf('16', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 2.40/2.63      inference('sup-', [status(thm)], ['13', '15'])).
% 2.40/2.63  thf('17', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2))),
% 2.40/2.63      inference('sup-', [status(thm)], ['12', '16'])).
% 2.40/2.63  thf('18', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['11', '17'])).
% 2.40/2.63  thf('19', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['10', '18'])).
% 2.40/2.63  thf('20', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((X0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ~ (zip_tseitin_0 @ (sk_D @ X0 @ sk_B_1) @ sk_A @ sk_A @ sk_A @ 
% 2.40/2.63               sk_A @ sk_A))),
% 2.40/2.63      inference('sup-', [status(thm)], ['9', '19'])).
% 2.40/2.63  thf('21', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_D @ X0 @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((sk_D @ X0 @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((sk_D @ X0 @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((sk_D @ X0 @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((sk_D @ X0 @ sk_B_1) = (sk_A))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['1', '20'])).
% 2.40/2.63  thf('22', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((X0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((sk_D @ X0 @ sk_B_1) = (sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['21'])).
% 2.40/2.63  thf('23', plain,
% 2.40/2.63      (![X43 : $i, X44 : $i]:
% 2.40/2.63         ((r2_hidden @ (sk_C_1 @ X43 @ X44) @ X43)
% 2.40/2.63          | ((sk_C_1 @ X43 @ X44) = (k1_funct_1 @ X44 @ (sk_D @ X43 @ X44)))
% 2.40/2.63          | ((X43) = (k2_relat_1 @ X44))
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (v1_relat_1 @ X44))),
% 2.40/2.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.40/2.63  thf('24', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('25', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X1)
% 2.40/2.63          | ~ (v1_funct_1 @ X1)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ X1))
% 2.40/2.63          | ((sk_C_1 @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_D @ X0 @ X1)))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['23', '24'])).
% 2.40/2.63  thf('26', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_C_1 @ X0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63          | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63          | ~ (v1_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup+', [status(thm)], ['22', '25'])).
% 2.40/2.63  thf('27', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('28', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('29', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_C_1 @ X0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.40/2.63  thf('30', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((X0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((sk_C_1 @ X0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['29'])).
% 2.40/2.63  thf(t65_relat_1, axiom,
% 2.40/2.63    (![A:$i]:
% 2.40/2.63     ( ( v1_relat_1 @ A ) =>
% 2.40/2.63       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 2.40/2.63         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 2.40/2.63  thf('31', plain,
% 2.40/2.63      (![X42 : $i]:
% 2.40/2.63         (((k2_relat_1 @ X42) != (k1_xboole_0))
% 2.40/2.63          | ((k1_relat_1 @ X42) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_relat_1 @ X42))),
% 2.40/2.63      inference('cnf', [status(esa)], [t65_relat_1])).
% 2.40/2.63  thf('32', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((X0) != (k1_xboole_0))
% 2.40/2.63          | ((sk_C_1 @ X0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ sk_B_1)
% 2.40/2.63          | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['30', '31'])).
% 2.40/2.63  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('34', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('35', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((X0) != (k1_xboole_0))
% 2.40/2.63          | ((sk_C_1 @ X0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 2.40/2.63      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.40/2.63  thf('36', plain,
% 2.40/2.63      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63        | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.63        | ((sk_C_1 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['35'])).
% 2.40/2.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.40/2.63  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.63  thf('38', plain,
% 2.40/2.63      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63        | ((sk_C_1 @ k1_xboole_0 @ sk_B_1) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 2.40/2.63      inference('simplify_reflect+', [status(thm)], ['36', '37'])).
% 2.40/2.63  thf('39', plain,
% 2.40/2.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.63         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 2.40/2.63          | ((X27) = (X28))
% 2.40/2.63          | ((X27) = (X29))
% 2.40/2.63          | ((X27) = (X30))
% 2.40/2.63          | ((X27) = (X31))
% 2.40/2.63          | ((X27) = (X32)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.63  thf('40', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 2.40/2.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.40/2.63  thf('41', plain,
% 2.40/2.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('42', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['11', '17'])).
% 2.40/2.63  thf('43', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ (sk_B @ (k2_tarski @ X1 @ X0)) @ X0 @ X1 @ X1 @ 
% 2.40/2.63               X1 @ X1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['41', '42'])).
% 2.40/2.63  thf('44', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0 @ X0 @ X0)
% 2.40/2.63          | (v1_xboole_0 @ (k2_tarski @ X0 @ X0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['40', '43'])).
% 2.40/2.63  thf('45', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | (v1_xboole_0 @ (k2_tarski @ X0 @ X0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['39', '44'])).
% 2.40/2.63  thf('46', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k2_tarski @ X0 @ X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['45'])).
% 2.40/2.63  thf(l44_zfmisc_1, axiom,
% 2.40/2.63    (![A:$i,B:$i]:
% 2.40/2.63     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.40/2.63          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 2.40/2.63  thf('47', plain,
% 2.40/2.63      (![X24 : $i, X25 : $i]:
% 2.40/2.63         (((X24) = (k1_xboole_0))
% 2.40/2.63          | (r2_hidden @ (sk_C @ X25 @ X24) @ X24)
% 2.40/2.63          | ((X24) = (k1_tarski @ X25)))),
% 2.40/2.63      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 2.40/2.63  thf('48', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('49', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (((X0) = (k1_tarski @ X1))
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['47', '48'])).
% 2.40/2.63  thf('50', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 2.40/2.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.40/2.63  thf('51', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (((k2_tarski @ X1 @ X1) = (X0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['49', '50'])).
% 2.40/2.63  thf('52', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 2.40/2.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.40/2.63  thf('53', plain,
% 2.40/2.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.63         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 2.40/2.63          | ((X27) = (X28))
% 2.40/2.63          | ((X27) = (X29))
% 2.40/2.63          | ((X27) = (X30))
% 2.40/2.63          | ((X27) = (X31))
% 2.40/2.63          | ((X27) = (X32)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.63  thf('54', plain,
% 2.40/2.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('55', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['10', '18'])).
% 2.40/2.63  thf('56', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k1_tarski @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0 @ X0 @ 
% 2.40/2.63               X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['54', '55'])).
% 2.40/2.63  thf('57', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['53', '56'])).
% 2.40/2.63  thf('58', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['57'])).
% 2.40/2.63  thf('59', plain,
% 2.40/2.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('60', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 2.40/2.63          | (v1_xboole_0 @ (k1_tarski @ X0))
% 2.40/2.63          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['58', '59'])).
% 2.40/2.63  thf('61', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k1_tarski @ X0))
% 2.40/2.63          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['60'])).
% 2.40/2.63  thf('62', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 2.40/2.63          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['52', '61'])).
% 2.40/2.63  thf('63', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('64', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k1_tarski @ X0))
% 2.40/2.63          | ~ (v1_xboole_0 @ (k2_tarski @ X0 @ X0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['62', '63'])).
% 2.40/2.63  thf('65', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | (v1_xboole_0 @ (k1_tarski @ X1)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['51', '64'])).
% 2.40/2.63  thf('66', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k1_tarski @ X1))
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('simplify', [status(thm)], ['65'])).
% 2.40/2.63  thf('67', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('68', plain,
% 2.40/2.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('69', plain,
% 2.40/2.63      (![X44 : $i, X46 : $i, X47 : $i]:
% 2.40/2.63         (((X46) != (k2_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ X47 @ X44) @ (k1_relat_1 @ X44))
% 2.40/2.63          | ~ (r2_hidden @ X47 @ X46)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (v1_relat_1 @ X44))),
% 2.40/2.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.40/2.63  thf('70', plain,
% 2.40/2.63      (![X44 : $i, X47 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X44)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (r2_hidden @ X47 @ (k2_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ X47 @ X44) @ (k1_relat_1 @ X44)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['69'])).
% 2.40/2.63  thf('71', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k2_relat_1 @ X0))
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ (sk_B @ (k2_relat_1 @ X0)) @ X0) @ 
% 2.40/2.63             (k1_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['68', '70'])).
% 2.40/2.63  thf('72', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('73', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X0)
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | (v1_xboole_0 @ (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['71', '72'])).
% 2.40/2.63  thf('74', plain,
% 2.40/2.63      ((~ (v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (v1_xboole_0 @ (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63        | ~ (v1_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['67', '73'])).
% 2.40/2.63  thf('75', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('76', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('77', plain,
% 2.40/2.63      ((~ (v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (v1_xboole_0 @ (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('demod', [status(thm)], ['74', '75', '76'])).
% 2.40/2.63  thf('78', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | (v1_xboole_0 @ (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['66', '77'])).
% 2.40/2.63  thf('79', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (((X0) = (k1_tarski @ X1))
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['47', '48'])).
% 2.40/2.63  thf('80', plain,
% 2.40/2.63      (((k2_relat_1 @ sk_B_1) != (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('81', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k2_relat_1 @ sk_B_1) != (X0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['79', '80'])).
% 2.40/2.63  thf('82', plain,
% 2.40/2.63      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['81'])).
% 2.40/2.63  thf('83', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['78', '82'])).
% 2.40/2.63  thf('84', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['46', '83'])).
% 2.40/2.63  thf('85', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 2.40/2.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.40/2.63  thf('86', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k1_xboole_0) = (k1_tarski @ X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['84', '85'])).
% 2.40/2.63  thf('87', plain,
% 2.40/2.63      (![X42 : $i]:
% 2.40/2.63         (((k2_relat_1 @ X42) != (k1_xboole_0))
% 2.40/2.63          | ((k1_relat_1 @ X42) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_relat_1 @ X42))),
% 2.40/2.63      inference('cnf', [status(esa)], [t65_relat_1])).
% 2.40/2.63  thf('88', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k1_xboole_0) != (k1_xboole_0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((k1_xboole_0) = (k1_tarski @ X0))
% 2.40/2.63          | ~ (v1_relat_1 @ sk_B_1)
% 2.40/2.63          | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['86', '87'])).
% 2.40/2.63  thf('89', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('90', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('91', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k1_xboole_0) != (k1_xboole_0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 2.40/2.63          | ((k1_xboole_0) = (k1_tarski @ X0))
% 2.40/2.63          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 2.40/2.63      inference('demod', [status(thm)], ['88', '89', '90'])).
% 2.40/2.63  thf('92', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63          | ((k1_xboole_0) = (k1_tarski @ X0))
% 2.40/2.63          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['91'])).
% 2.40/2.63  thf('93', plain,
% 2.40/2.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.63         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 2.40/2.63          | ((X27) = (X28))
% 2.40/2.63          | ((X27) = (X29))
% 2.40/2.63          | ((X27) = (X30))
% 2.40/2.63          | ((X27) = (X31))
% 2.40/2.63          | ((X27) = (X32)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.63  thf('94', plain,
% 2.40/2.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('95', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('96', plain,
% 2.40/2.63      (![X44 : $i, X46 : $i, X48 : $i, X49 : $i]:
% 2.40/2.63         (((X46) != (k2_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ X48 @ X46)
% 2.40/2.63          | ~ (r2_hidden @ X49 @ (k1_relat_1 @ X44))
% 2.40/2.63          | ((X48) != (k1_funct_1 @ X44 @ X49))
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (v1_relat_1 @ X44))),
% 2.40/2.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.40/2.63  thf('97', plain,
% 2.40/2.63      (![X44 : $i, X49 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X44)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (r2_hidden @ X49 @ (k1_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ (k1_funct_1 @ X44 @ X49) @ (k2_relat_1 @ X44)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['96'])).
% 2.40/2.63  thf('98', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.40/2.63          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ X0) @ (k2_relat_1 @ sk_B_1))
% 2.40/2.63          | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63          | ~ (v1_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['95', '97'])).
% 2.40/2.63  thf('99', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('100', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('101', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.40/2.63          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ X0) @ (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('demod', [status(thm)], ['98', '99', '100'])).
% 2.40/2.63  thf('102', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63           (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['94', '101'])).
% 2.40/2.63  thf('103', plain,
% 2.40/2.63      (![X44 : $i, X47 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X44)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (r2_hidden @ X47 @ (k2_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ X47 @ X44) @ (k1_relat_1 @ X44)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['69'])).
% 2.40/2.63  thf('104', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (r2_hidden @ 
% 2.40/2.63           (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63            sk_B_1) @ 
% 2.40/2.63           (k1_relat_1 @ sk_B_1))
% 2.40/2.63        | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63        | ~ (v1_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['102', '103'])).
% 2.40/2.63  thf('105', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('106', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('107', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('108', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (r2_hidden @ 
% 2.40/2.63           (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63            sk_B_1) @ 
% 2.40/2.63           (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 2.40/2.63  thf('109', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['10', '18'])).
% 2.40/2.63  thf('110', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | ~ (zip_tseitin_0 @ 
% 2.40/2.63             (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63              sk_B_1) @ 
% 2.40/2.63             sk_A @ sk_A @ sk_A @ sk_A @ sk_A))),
% 2.40/2.63      inference('sup-', [status(thm)], ['108', '109'])).
% 2.40/2.63  thf('111', plain,
% 2.40/2.63      ((((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ sk_B_1)
% 2.40/2.63          = (sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63            sk_B_1) = (sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63            sk_B_1) = (sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63            sk_B_1) = (sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63            sk_B_1) = (sk_A))
% 2.40/2.63        | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['93', '110'])).
% 2.40/2.63  thf('112', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63            sk_B_1) = (sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['111'])).
% 2.40/2.63  thf('113', plain,
% 2.40/2.63      ((((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A))
% 2.40/2.63        | ((k1_xboole_0) = (k1_tarski @ sk_A))
% 2.40/2.63        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63        | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['92', '112'])).
% 2.40/2.63  thf('114', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | ((k1_xboole_0) = (k1_tarski @ sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['113'])).
% 2.40/2.63  thf('115', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['78', '82'])).
% 2.40/2.63  thf('116', plain,
% 2.40/2.63      (![X42 : $i]:
% 2.40/2.63         (((k2_relat_1 @ X42) != (k1_xboole_0))
% 2.40/2.63          | ((k1_relat_1 @ X42) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_relat_1 @ X42))),
% 2.40/2.63      inference('cnf', [status(esa)], [t65_relat_1])).
% 2.40/2.63  thf('117', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k1_xboole_0) != (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_relat_1 @ sk_B_1)
% 2.40/2.63          | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['115', '116'])).
% 2.40/2.63  thf('118', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('119', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('120', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k1_xboole_0) != (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0)
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 2.40/2.63      inference('demod', [status(thm)], ['117', '118', '119'])).
% 2.40/2.63  thf('121', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('simplify', [status(thm)], ['120'])).
% 2.40/2.63  thf('122', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (((X0) = (k1_tarski @ X1))
% 2.40/2.63          | ((X0) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['47', '48'])).
% 2.40/2.63  thf('123', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (((k1_tarski @ X0) != (k1_xboole_0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X1)
% 2.40/2.63          | ((X1) = (k1_xboole_0)))),
% 2.40/2.63      inference('eq_fact', [status(thm)], ['122'])).
% 2.40/2.63  thf('124', plain,
% 2.40/2.63      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.40/2.63      inference('clc', [status(thm)], ['121', '123'])).
% 2.40/2.63  thf('125', plain,
% 2.40/2.63      ((((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A))
% 2.40/2.63        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('clc', [status(thm)], ['114', '124'])).
% 2.40/2.63  thf('126', plain,
% 2.40/2.63      ((((sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_B_1) @ sk_B_1) = (sk_A))
% 2.40/2.63        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['38', '125'])).
% 2.40/2.63  thf('127', plain,
% 2.40/2.63      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63        | ((sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_B_1) @ sk_B_1) = (sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['126'])).
% 2.40/2.63  thf('128', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X1)
% 2.40/2.63          | ~ (v1_funct_1 @ X1)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ X1))
% 2.40/2.63          | ((sk_C_1 @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_D @ X0 @ X1)))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['23', '24'])).
% 2.40/2.63  thf('129', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X1)
% 2.40/2.63          | ~ (v1_funct_1 @ X1)
% 2.40/2.63          | ((X0) = (k2_relat_1 @ X1))
% 2.40/2.63          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k1_relat_1 @ X1))
% 2.40/2.63          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['3', '4'])).
% 2.40/2.63  thf('130', plain,
% 2.40/2.63      (![X44 : $i, X49 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X44)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (r2_hidden @ X49 @ (k1_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ (k1_funct_1 @ X44 @ X49) @ (k2_relat_1 @ X44)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['96'])).
% 2.40/2.63  thf('131', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (v1_xboole_0 @ X1)
% 2.40/2.63          | ((X1) = (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0)
% 2.40/2.63          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 2.40/2.63             (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['129', '130'])).
% 2.40/2.63  thf('132', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_relat_1 @ X0)
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ((X1) = (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('simplify', [status(thm)], ['131'])).
% 2.40/2.63  thf('133', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X1)
% 2.40/2.63          | ((X1) = (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0)
% 2.40/2.63          | ~ (v1_xboole_0 @ X1)
% 2.40/2.63          | ((X1) = (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0))),
% 2.40/2.63      inference('sup+', [status(thm)], ['128', '132'])).
% 2.40/2.63  thf('134', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X0)
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ((X1) = (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X1)
% 2.40/2.63          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['133'])).
% 2.40/2.63  thf('135', plain,
% 2.40/2.63      (![X44 : $i, X47 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X44)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (r2_hidden @ X47 @ (k2_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ X47 @ X44) @ (k1_relat_1 @ X44)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['69'])).
% 2.40/2.63  thf('136', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (v1_xboole_0 @ X1)
% 2.40/2.63          | ((X1) = (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0)
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ X1 @ X0) @ X0) @ (k1_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['134', '135'])).
% 2.40/2.63  thf('137', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ X1 @ X0) @ X0) @ (k1_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_relat_1 @ X0)
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ((X1) = (k2_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('simplify', [status(thm)], ['136'])).
% 2.40/2.63  thf('138', plain,
% 2.40/2.63      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))
% 2.40/2.63        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63        | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.63        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63        | ~ (v1_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup+', [status(thm)], ['127', '137'])).
% 2.40/2.63  thf('139', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('140', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.63  thf('141', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('142', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('143', plain,
% 2.40/2.63      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 2.40/2.63        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 2.40/2.63        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 2.40/2.63  thf('144', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('145', plain,
% 2.40/2.63      (![X42 : $i]:
% 2.40/2.63         (((k1_relat_1 @ X42) != (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ X42) = (k1_xboole_0))
% 2.40/2.63          | ~ (v1_relat_1 @ X42))),
% 2.40/2.63      inference('cnf', [status(esa)], [t65_relat_1])).
% 2.40/2.63  thf('146', plain,
% 2.40/2.63      ((((k1_tarski @ sk_A) != (k1_xboole_0))
% 2.40/2.63        | ~ (v1_relat_1 @ sk_B_1)
% 2.40/2.63        | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['144', '145'])).
% 2.40/2.63  thf('147', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('148', plain,
% 2.40/2.63      ((((k1_tarski @ sk_A) != (k1_xboole_0))
% 2.40/2.63        | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('demod', [status(thm)], ['146', '147'])).
% 2.40/2.63  thf('149', plain,
% 2.40/2.63      ((((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('clc', [status(thm)], ['143', '148'])).
% 2.40/2.63  thf('150', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.40/2.63          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ X0) @ (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('demod', [status(thm)], ['98', '99', '100'])).
% 2.40/2.63  thf('151', plain,
% 2.40/2.63      ((((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['149', '150'])).
% 2.40/2.63  thf('152', plain,
% 2.40/2.63      (![X44 : $i, X47 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X44)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (r2_hidden @ X47 @ (k2_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ X47 @ X44) @ (k1_relat_1 @ X44)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['69'])).
% 2.40/2.63  thf('153', plain,
% 2.40/2.63      ((((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | (r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 2.40/2.63           (k1_relat_1 @ sk_B_1))
% 2.40/2.63        | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63        | ~ (v1_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['151', '152'])).
% 2.40/2.63  thf('154', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('155', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('156', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('157', plain,
% 2.40/2.63      ((((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | (r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 2.40/2.63           (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 2.40/2.63  thf('158', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['10', '18'])).
% 2.40/2.63  thf('159', plain,
% 2.40/2.63      ((((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | ~ (zip_tseitin_0 @ 
% 2.40/2.63             (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) @ sk_A @ sk_A @ 
% 2.40/2.63             sk_A @ sk_A @ sk_A))),
% 2.40/2.63      inference('sup-', [status(thm)], ['157', '158'])).
% 2.40/2.63  thf('160', plain,
% 2.40/2.63      ((((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A))
% 2.40/2.63        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['0', '159'])).
% 2.40/2.63  thf('161', plain,
% 2.40/2.63      ((((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | ((sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) = (sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['160'])).
% 2.40/2.63  thf('162', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['57'])).
% 2.40/2.63  thf('163', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (r2_hidden @ 
% 2.40/2.63           (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 2.40/2.63            sk_B_1) @ 
% 2.40/2.63           (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 2.40/2.63  thf('164', plain,
% 2.40/2.63      (((r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 2.40/2.63         (k1_tarski @ sk_A))
% 2.40/2.63        | (v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['162', '163'])).
% 2.40/2.63  thf('165', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 2.40/2.63           (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['164'])).
% 2.40/2.63  thf('166', plain,
% 2.40/2.63      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 2.40/2.63        | ((k1_xboole_0) = (k2_relat_1 @ sk_B_1))
% 2.40/2.63        | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['161', '165'])).
% 2.40/2.63  thf('167', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((v1_xboole_0 @ (k1_tarski @ X0))
% 2.40/2.63          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['60'])).
% 2.40/2.63  thf('168', plain,
% 2.40/2.63      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 2.40/2.63        | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 2.40/2.63      inference('clc', [status(thm)], ['166', '167'])).
% 2.40/2.63  thf('169', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 2.40/2.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.40/2.63  thf('170', plain,
% 2.40/2.63      (![X4 : $i, X5 : $i]:
% 2.40/2.63         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 2.40/2.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.40/2.63  thf('171', plain,
% 2.40/2.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.40/2.63         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 2.40/2.63      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.40/2.63  thf('172', plain,
% 2.40/2.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.40/2.63         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 2.40/2.63           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 2.40/2.63      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.40/2.63  thf('173', plain,
% 2.40/2.63      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.40/2.63         ((zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 2.40/2.63          | (r2_hidden @ X33 @ X39)
% 2.40/2.63          | ((X39) != (k3_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.40/2.63  thf('174', plain,
% 2.40/2.63      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.40/2.63         ((r2_hidden @ X33 @ (k3_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34))
% 2.40/2.63          | (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38))),
% 2.40/2.63      inference('simplify', [status(thm)], ['173'])).
% 2.40/2.63  thf('175', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.40/2.63         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 2.40/2.63          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 2.40/2.63      inference('sup+', [status(thm)], ['172', '174'])).
% 2.40/2.63  thf('176', plain,
% 2.40/2.63      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.40/2.63         (((X27) != (X26))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X26))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.63  thf('177', plain,
% 2.40/2.63      (![X26 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.40/2.63         ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X30 @ X31 @ X26)),
% 2.40/2.63      inference('simplify', [status(thm)], ['176'])).
% 2.40/2.63  thf('178', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.40/2.63         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 2.40/2.63      inference('sup-', [status(thm)], ['175', '177'])).
% 2.40/2.63  thf('179', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('180', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.40/2.63         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['178', '179'])).
% 2.40/2.63  thf('181', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.63         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['171', '180'])).
% 2.40/2.63  thf('182', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['170', '181'])).
% 2.40/2.63  thf('183', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['169', '182'])).
% 2.40/2.63  thf('184', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 2.40/2.63      inference('clc', [status(thm)], ['168', '183'])).
% 2.40/2.63  thf('185', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.40/2.63          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ X0) @ (k2_relat_1 @ sk_B_1)))),
% 2.40/2.63      inference('demod', [status(thm)], ['98', '99', '100'])).
% 2.40/2.63  thf('186', plain,
% 2.40/2.63      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['184', '185'])).
% 2.40/2.63  thf('187', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.63  thf('188', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_B_1))),
% 2.40/2.63      inference('sup-', [status(thm)], ['186', '187'])).
% 2.40/2.63  thf('189', plain,
% 2.40/2.63      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.63         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 2.40/2.63          | ((X27) = (X28))
% 2.40/2.63          | ((X27) = (X29))
% 2.40/2.63          | ((X27) = (X30))
% 2.40/2.63          | ((X27) = (X31))
% 2.40/2.63          | ((X27) = (X32)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.63  thf('190', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('191', plain,
% 2.40/2.63      (![X24 : $i, X25 : $i]:
% 2.40/2.63         (((X24) = (k1_xboole_0))
% 2.40/2.63          | (r2_hidden @ (sk_C @ X25 @ X24) @ X24)
% 2.40/2.63          | ((X24) = (k1_tarski @ X25)))),
% 2.40/2.63      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 2.40/2.63  thf('192', plain,
% 2.40/2.63      (![X44 : $i, X47 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X44)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (r2_hidden @ X47 @ (k2_relat_1 @ X44))
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ X47 @ X44) @ (k1_relat_1 @ X44)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['69'])).
% 2.40/2.63  thf('193', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 2.40/2.63          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.40/2.63          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 2.40/2.63             (k1_relat_1 @ X0))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['191', '192'])).
% 2.40/2.63  thf('194', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((r2_hidden @ 
% 2.40/2.63           (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) @ 
% 2.40/2.63           (k1_tarski @ sk_A))
% 2.40/2.63          | ~ (v1_relat_1 @ sk_B_1)
% 2.40/2.63          | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['190', '193'])).
% 2.40/2.63  thf('195', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('196', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('197', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         ((r2_hidden @ 
% 2.40/2.63           (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) @ 
% 2.40/2.63           (k1_tarski @ sk_A))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0)))),
% 2.40/2.63      inference('demod', [status(thm)], ['194', '195', '196'])).
% 2.40/2.63  thf('198', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['10', '18'])).
% 2.40/2.63  thf('199', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ~ (zip_tseitin_0 @ 
% 2.40/2.63               (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) @ 
% 2.40/2.63               sk_A @ sk_A @ sk_A @ sk_A @ sk_A))),
% 2.40/2.63      inference('sup-', [status(thm)], ['197', '198'])).
% 2.40/2.63  thf('200', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['189', '199'])).
% 2.40/2.63  thf('201', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) @ sk_B_1) = (sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['200'])).
% 2.40/2.63  thf('202', plain,
% 2.40/2.63      (![X24 : $i, X25 : $i]:
% 2.40/2.63         (((X24) = (k1_xboole_0))
% 2.40/2.63          | (r2_hidden @ (sk_C @ X25 @ X24) @ X24)
% 2.40/2.63          | ((X24) = (k1_tarski @ X25)))),
% 2.40/2.63      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 2.40/2.63  thf('203', plain,
% 2.40/2.63      (![X44 : $i, X46 : $i, X47 : $i]:
% 2.40/2.63         (((X46) != (k2_relat_1 @ X44))
% 2.40/2.63          | ((X47) = (k1_funct_1 @ X44 @ (sk_D_1 @ X47 @ X44)))
% 2.40/2.63          | ~ (r2_hidden @ X47 @ X46)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (v1_relat_1 @ X44))),
% 2.40/2.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.40/2.63  thf('204', plain,
% 2.40/2.63      (![X44 : $i, X47 : $i]:
% 2.40/2.63         (~ (v1_relat_1 @ X44)
% 2.40/2.63          | ~ (v1_funct_1 @ X44)
% 2.40/2.63          | ~ (r2_hidden @ X47 @ (k2_relat_1 @ X44))
% 2.40/2.63          | ((X47) = (k1_funct_1 @ X44 @ (sk_D_1 @ X47 @ X44))))),
% 2.40/2.63      inference('simplify', [status(thm)], ['203'])).
% 2.40/2.63  thf('205', plain,
% 2.40/2.63      (![X0 : $i, X1 : $i]:
% 2.40/2.63         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 2.40/2.63          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.40/2.63          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 2.40/2.63              = (k1_funct_1 @ X0 @ 
% 2.40/2.63                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 2.40/2.63          | ~ (v1_funct_1 @ X0)
% 2.40/2.63          | ~ (v1_relat_1 @ X0))),
% 2.40/2.63      inference('sup-', [status(thm)], ['202', '204'])).
% 2.40/2.63  thf('206', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 2.40/2.63          | ~ (v1_relat_1 @ sk_B_1)
% 2.40/2.63          | ~ (v1_funct_1 @ sk_B_1)
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0)))),
% 2.40/2.63      inference('sup+', [status(thm)], ['201', '205'])).
% 2.40/2.63  thf('207', plain, ((v1_relat_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('208', plain, ((v1_funct_1 @ sk_B_1)),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('209', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0)))),
% 2.40/2.63      inference('demod', [status(thm)], ['206', '207', '208'])).
% 2.40/2.63  thf('210', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['209'])).
% 2.40/2.63  thf('211', plain,
% 2.40/2.63      (![X24 : $i, X25 : $i]:
% 2.40/2.63         (((X24) = (k1_xboole_0))
% 2.40/2.63          | ((sk_C @ X25 @ X24) != (X25))
% 2.40/2.63          | ((X24) = (k1_tarski @ X25)))),
% 2.40/2.63      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 2.40/2.63  thf('212', plain,
% 2.40/2.63      (![X0 : $i]:
% 2.40/2.63         (((k1_funct_1 @ sk_B_1 @ sk_A) != (X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 2.40/2.63          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('sup-', [status(thm)], ['210', '211'])).
% 2.40/2.63  thf('213', plain,
% 2.40/2.63      ((((k2_relat_1 @ sk_B_1) = (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)))
% 2.40/2.63        | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 2.40/2.63      inference('simplify', [status(thm)], ['212'])).
% 2.40/2.63  thf('214', plain,
% 2.40/2.63      (((k2_relat_1 @ sk_B_1) != (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 2.40/2.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.63  thf('215', plain, (((k2_relat_1 @ sk_B_1) = (k1_xboole_0))),
% 2.40/2.63      inference('simplify_reflect-', [status(thm)], ['213', '214'])).
% 2.40/2.63  thf('216', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.63  thf('217', plain, ($false),
% 2.40/2.63      inference('demod', [status(thm)], ['188', '215', '216'])).
% 2.40/2.63  
% 2.40/2.63  % SZS output end Refutation
% 2.40/2.63  
% 2.40/2.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
