%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dKhJF3HW6F

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:26 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  169 (1167 expanded)
%              Number of leaves         :   34 ( 361 expanded)
%              Depth                    :   32
%              Number of atoms          : 2133 (16789 expanded)
%              Number of equality atoms :  156 (1391 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d5_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( ( I != G )
              & ( I != F )
              & ( I != E )
              & ( I != D )
              & ( I != C )
              & ( I != B )
              & ( I != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [I: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( I != A )
        & ( I != B )
        & ( I != C )
        & ( I != D )
        & ( I != E )
        & ( I != F )
        & ( I != G ) ) ) )).

thf('0',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 )
      | ( X29 = X33 )
      | ( X29 = X34 )
      | ( X29 = X35 )
      | ( X29 = X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('2',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ ( sk_C @ X48 @ X49 ) @ X48 )
      | ( ( sk_C @ X48 @ X49 )
        = ( k1_funct_1 @ X49 @ ( sk_D @ X48 @ X49 ) ) )
      | ( X48
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ ( sk_C @ X48 @ X49 ) @ X48 )
      | ( r2_hidden @ ( sk_D @ X48 @ X49 ) @ ( k1_relat_1 @ X49 ) )
      | ( X48
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X55 @ ( k1_relat_1 @ X56 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X56 @ X55 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X46 @ X45 )
      | ~ ( zip_tseitin_0 @ X46 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      | ( X45
       != ( k5_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      | ~ ( r2_hidden @ X46 @ ( k5_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 ) @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('36',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      | ( r2_hidden @ X37 @ X45 )
      | ( X45
       != ( k5_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X37 @ ( k5_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 @ X38 ) )
      | ( zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup+',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X28 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','44'])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X55 @ ( k1_relat_1 @ X56 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X56 @ X55 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( X51
       != ( k2_relat_1 @ X49 ) )
      | ( X52
        = ( k1_funct_1 @ X49 @ ( sk_D_1 @ X52 @ X49 ) ) )
      | ~ ( r2_hidden @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('54',plain,(
    ! [X49: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( r2_hidden @ X52 @ ( k2_relat_1 @ X49 ) )
      | ( X52
        = ( k1_funct_1 @ X49 @ ( sk_D_1 @ X52 @ X49 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ( k1_funct_1 @ sk_B @ sk_A )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ ( sk_C @ X48 @ X49 ) @ X48 )
      | ( ( sk_C @ X48 @ X49 )
        = ( k1_funct_1 @ X49 @ ( sk_D @ X48 @ X49 ) ) )
      | ( X48
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ ( sk_C @ X48 @ X49 ) @ X48 )
      | ( r2_hidden @ ( sk_D @ X48 @ X49 ) @ ( k1_relat_1 @ X49 ) )
      | ( X48
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X48 @ X49 ) @ X48 )
      | ( ( sk_C @ X48 @ X49 )
       != ( k1_funct_1 @ X49 @ X50 ) )
      | ~ ( r2_hidden @ X50 @ ( k1_relat_1 @ X49 ) )
      | ( X48
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ( ( sk_C @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','79'])).

thf('81',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('82',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( X51
       != ( k2_relat_1 @ X49 ) )
      | ( r2_hidden @ ( sk_D_1 @ X52 @ X49 ) @ ( k1_relat_1 @ X49 ) )
      | ~ ( r2_hidden @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('83',plain,(
    ! [X49: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( r2_hidden @ X52 @ ( k2_relat_1 @ X49 ) )
      | ( r2_hidden @ ( sk_D_1 @ X52 @ X49 ) @ ( k1_relat_1 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('88',plain,(
    r2_hidden @ ( sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('92',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( k1_tarski @ X0 ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ ( k2_tarski @ X0 @ X0 ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('96',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('99',plain,
    ( ( r2_hidden @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('102',plain,(
    r2_hidden @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X49: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( r2_hidden @ X52 @ ( k2_relat_1 @ X49 ) )
      | ( X52
        = ( k1_funct_1 @ X49 @ ( sk_D_1 @ X52 @ X49 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('104',plain,
    ( ( ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('106',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('107',plain,
    ( ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 )
      | ( X29 = X33 )
      | ( X29 = X34 )
      | ( X29 = X35 )
      | ( X29 = X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    r2_hidden @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('110',plain,(
    ! [X49: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( r2_hidden @ X52 @ ( k2_relat_1 @ X49 ) )
      | ( r2_hidden @ ( sk_D_1 @ X52 @ X49 ) @ ( k1_relat_1 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('111',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('113',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('114',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('115',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('117',plain,(
    ~ ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B ) @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B )
      = sk_A )
    | ( ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B )
      = sk_A )
    | ( ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B )
      = sk_A )
    | ( ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B )
      = sk_A )
    | ( ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B )
      = sk_A )
    | ( ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B )
      = sk_A )
    | ( ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['108','117'])).

thf('119',plain,
    ( ( sk_D_1 @ ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ sk_B )
    = sk_A ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['107','119'])).

thf('121',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X48 @ X49 ) @ X48 )
      | ( ( sk_C @ X48 @ X49 )
       != ( k1_funct_1 @ X49 @ X50 ) )
      | ~ ( r2_hidden @ X50 @ ( k1_relat_1 @ X49 ) )
      | ( X48
        = ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','44'])).

thf('124',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('125',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('126',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('127',plain,
    ( ( sk_C @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['107','119'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127'])).

thf('129',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','44'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['131','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dKhJF3HW6F
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.60/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.76  % Solved by: fo/fo7.sh
% 0.60/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.76  % done 305 iterations in 0.305s
% 0.60/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.76  % SZS output start Refutation
% 0.60/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.76  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.60/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.60/0.76  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.60/0.76                                           $i > $i).
% 0.60/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.76  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.60/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.76  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.60/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.60/0.76                                               $i > $i > $o).
% 0.60/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.76  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.60/0.76  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.60/0.76  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.60/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.76  thf(d5_enumset1, axiom,
% 0.60/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.60/0.76     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.60/0.76       ( ![I:$i]:
% 0.60/0.76         ( ( r2_hidden @ I @ H ) <=>
% 0.60/0.76           ( ~( ( ( I ) != ( G ) ) & ( ( I ) != ( F ) ) & ( ( I ) != ( E ) ) & 
% 0.60/0.76                ( ( I ) != ( D ) ) & ( ( I ) != ( C ) ) & ( ( I ) != ( B ) ) & 
% 0.60/0.76                ( ( I ) != ( A ) ) ) ) ) ) ))).
% 0.60/0.76  thf(zf_stmt_0, axiom,
% 0.60/0.76    (![I:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.60/0.76     ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.60/0.76       ( ( ( I ) != ( A ) ) & ( ( I ) != ( B ) ) & ( ( I ) != ( C ) ) & 
% 0.60/0.76         ( ( I ) != ( D ) ) & ( ( I ) != ( E ) ) & ( ( I ) != ( F ) ) & 
% 0.60/0.76         ( ( I ) != ( G ) ) ) ))).
% 0.60/0.76  thf('0', plain,
% 0.60/0.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 0.60/0.76         X36 : $i]:
% 0.60/0.76         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.60/0.76          | ((X29) = (X30))
% 0.60/0.76          | ((X29) = (X31))
% 0.60/0.76          | ((X29) = (X32))
% 0.60/0.76          | ((X29) = (X33))
% 0.60/0.76          | ((X29) = (X34))
% 0.60/0.76          | ((X29) = (X35))
% 0.60/0.76          | ((X29) = (X36)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf(t69_enumset1, axiom,
% 0.60/0.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.76  thf('1', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.76  thf(d5_funct_1, axiom,
% 0.60/0.76    (![A:$i]:
% 0.60/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.76       ( ![B:$i]:
% 0.60/0.76         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.60/0.76           ( ![C:$i]:
% 0.60/0.76             ( ( r2_hidden @ C @ B ) <=>
% 0.60/0.76               ( ?[D:$i]:
% 0.60/0.76                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.60/0.76                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.60/0.76  thf('2', plain,
% 0.60/0.76      (![X48 : $i, X49 : $i]:
% 0.60/0.76         ((r2_hidden @ (sk_C @ X48 @ X49) @ X48)
% 0.60/0.76          | ((sk_C @ X48 @ X49) = (k1_funct_1 @ X49 @ (sk_D @ X48 @ X49)))
% 0.60/0.76          | ((X48) = (k2_relat_1 @ X49))
% 0.60/0.76          | ~ (v1_funct_1 @ X49)
% 0.60/0.76          | ~ (v1_relat_1 @ X49))),
% 0.60/0.76      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.76  thf('3', plain,
% 0.60/0.76      (![X48 : $i, X49 : $i]:
% 0.60/0.76         ((r2_hidden @ (sk_C @ X48 @ X49) @ X48)
% 0.60/0.76          | (r2_hidden @ (sk_D @ X48 @ X49) @ (k1_relat_1 @ X49))
% 0.60/0.76          | ((X48) = (k2_relat_1 @ X49))
% 0.60/0.76          | ~ (v1_funct_1 @ X49)
% 0.60/0.76          | ~ (v1_relat_1 @ X49))),
% 0.60/0.76      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.76  thf(t12_funct_1, axiom,
% 0.60/0.76    (![A:$i,B:$i]:
% 0.60/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.76       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.60/0.76         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.60/0.76  thf('4', plain,
% 0.60/0.76      (![X55 : $i, X56 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X55 @ (k1_relat_1 @ X56))
% 0.60/0.77          | (r2_hidden @ (k1_funct_1 @ X56 @ X55) @ (k2_relat_1 @ X56))
% 0.60/0.77          | ~ (v1_funct_1 @ X56)
% 0.60/0.77          | ~ (v1_relat_1 @ X56))),
% 0.60/0.77      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.60/0.77  thf('5', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (v1_relat_1 @ X0)
% 0.60/0.77          | ~ (v1_funct_1 @ X0)
% 0.60/0.77          | ((X1) = (k2_relat_1 @ X0))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.60/0.77          | ~ (v1_relat_1 @ X0)
% 0.60/0.77          | ~ (v1_funct_1 @ X0)
% 0.60/0.77          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 0.60/0.77             (k2_relat_1 @ X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.77  thf('6', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.60/0.77          | ((X1) = (k2_relat_1 @ X0))
% 0.60/0.77          | ~ (v1_funct_1 @ X0)
% 0.60/0.77          | ~ (v1_relat_1 @ X0))),
% 0.60/0.77      inference('simplify', [status(thm)], ['5'])).
% 0.60/0.77  thf('7', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0))
% 0.60/0.77          | ~ (v1_relat_1 @ X0)
% 0.60/0.77          | ~ (v1_funct_1 @ X0)
% 0.60/0.77          | ((X1) = (k2_relat_1 @ X0))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.60/0.77          | ~ (v1_relat_1 @ X0)
% 0.60/0.77          | ~ (v1_funct_1 @ X0)
% 0.60/0.77          | ((X1) = (k2_relat_1 @ X0))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.60/0.77      inference('sup+', [status(thm)], ['2', '6'])).
% 0.60/0.77  thf('8', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.60/0.77          | ((X1) = (k2_relat_1 @ X0))
% 0.60/0.77          | ~ (v1_funct_1 @ X0)
% 0.60/0.77          | ~ (v1_relat_1 @ X0)
% 0.60/0.77          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['7'])).
% 0.60/0.77  thf('9', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.77  thf(t70_enumset1, axiom,
% 0.60/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.60/0.77  thf('10', plain,
% 0.60/0.77      (![X1 : $i, X2 : $i]:
% 0.60/0.77         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.60/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.77  thf(t71_enumset1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.60/0.77  thf('11', plain,
% 0.60/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.77         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.60/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.60/0.77  thf(t75_enumset1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.60/0.77     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.60/0.77       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.60/0.77  thf('12', plain,
% 0.60/0.77      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.77         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.60/0.77           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.60/0.77      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.60/0.77  thf(t74_enumset1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.60/0.77     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.60/0.77       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.60/0.77  thf('13', plain,
% 0.60/0.77      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.60/0.77         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.60/0.77           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.60/0.77      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.60/0.77  thf('14', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.77         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.77           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['12', '13'])).
% 0.60/0.77  thf(t73_enumset1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.60/0.77     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.60/0.77       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.60/0.77  thf('15', plain,
% 0.60/0.77      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.60/0.77         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.60/0.77           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.60/0.77      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.60/0.77  thf('16', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.77         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.77           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['14', '15'])).
% 0.60/0.77  thf(t72_enumset1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.77     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.60/0.77  thf('17', plain,
% 0.60/0.77      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.77         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.60/0.77           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.60/0.77      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.60/0.77  thf('18', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.77         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.77           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['16', '17'])).
% 0.60/0.77  thf('19', plain,
% 0.60/0.77      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.77         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.60/0.77           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.60/0.77      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.60/0.77  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.60/0.77      $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.60/0.77  thf(zf_stmt_2, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.60/0.77     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.60/0.77       ( ![I:$i]:
% 0.60/0.77         ( ( r2_hidden @ I @ H ) <=>
% 0.60/0.77           ( ~( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.60/0.77  thf('20', plain,
% 0.60/0.77      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.60/0.77         X45 : $i, X46 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X46 @ X45)
% 0.60/0.77          | ~ (zip_tseitin_0 @ X46 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.60/0.77          | ((X45) != (k5_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 @ X38)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.77  thf('21', plain,
% 0.60/0.77      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.60/0.77         X46 : $i]:
% 0.60/0.77         (~ (zip_tseitin_0 @ X46 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.60/0.77          | ~ (r2_hidden @ X46 @ 
% 0.60/0.77               (k5_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 @ X38)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['20'])).
% 0.60/0.77  thf('22', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X7 @ 
% 0.60/0.77             (k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.60/0.77      inference('sup-', [status(thm)], ['19', '21'])).
% 0.60/0.77  thf('23', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3))),
% 0.60/0.77      inference('sup-', [status(thm)], ['18', '22'])).
% 0.60/0.77  thf('24', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 0.60/0.77      inference('sup-', [status(thm)], ['11', '23'])).
% 0.60/0.77  thf('25', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1))),
% 0.60/0.77      inference('sup-', [status(thm)], ['10', '24'])).
% 0.60/0.77  thf('26', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['9', '25'])).
% 0.60/0.77  thf('27', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ (k1_tarski @ X0) @ X1) @ (k2_relat_1 @ X1))
% 0.60/0.77          | ~ (v1_relat_1 @ X1)
% 0.60/0.77          | ~ (v1_funct_1 @ X1)
% 0.60/0.77          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.60/0.77          | ~ (zip_tseitin_0 @ (sk_C @ (k1_tarski @ X0) @ X1) @ X0 @ X0 @ X0 @ 
% 0.60/0.77               X0 @ X0 @ X0 @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['8', '26'])).
% 0.60/0.77  thf('28', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (zip_tseitin_0 @ (sk_C @ (k2_tarski @ X0 @ X0) @ X1) @ X0 @ X0 @ 
% 0.60/0.77             X0 @ X0 @ X0 @ X0 @ X0)
% 0.60/0.77          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.60/0.77          | ~ (v1_funct_1 @ X1)
% 0.60/0.77          | ~ (v1_relat_1 @ X1)
% 0.60/0.77          | (r2_hidden @ (sk_C @ (k1_tarski @ X0) @ X1) @ (k2_relat_1 @ X1)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['1', '27'])).
% 0.60/0.77  thf('29', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (((sk_C @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 0.60/0.77          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 0.60/0.77          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 0.60/0.77          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 0.60/0.77          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 0.60/0.77          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 0.60/0.77          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 0.60/0.77          | (r2_hidden @ (sk_C @ (k1_tarski @ X0) @ X1) @ (k2_relat_1 @ X1))
% 0.60/0.77          | ~ (v1_relat_1 @ X1)
% 0.60/0.77          | ~ (v1_funct_1 @ X1)
% 0.60/0.77          | ((k1_tarski @ X0) = (k2_relat_1 @ X1)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['0', '28'])).
% 0.60/0.77  thf('30', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.60/0.77          | ~ (v1_funct_1 @ X1)
% 0.60/0.77          | ~ (v1_relat_1 @ X1)
% 0.60/0.77          | (r2_hidden @ (sk_C @ (k1_tarski @ X0) @ X1) @ (k2_relat_1 @ X1))
% 0.60/0.77          | ((sk_C @ (k2_tarski @ X0 @ X0) @ X1) = (X0)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['29'])).
% 0.60/0.77  thf('31', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.77  thf('32', plain,
% 0.60/0.77      (![X1 : $i, X2 : $i]:
% 0.60/0.77         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.60/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.77  thf('33', plain,
% 0.60/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.77         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.60/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.60/0.77  thf('34', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.77         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.77           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['16', '17'])).
% 0.60/0.77  thf('35', plain,
% 0.60/0.77      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.77         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.60/0.77           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.60/0.77      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.60/0.77  thf('36', plain,
% 0.60/0.77      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 0.60/0.77         X44 : $i, X45 : $i]:
% 0.60/0.77         ((zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.60/0.77          | (r2_hidden @ X37 @ X45)
% 0.60/0.77          | ((X45) != (k5_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 @ X38)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.77  thf('37', plain,
% 0.60/0.77      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 0.60/0.77         X44 : $i]:
% 0.60/0.77         ((r2_hidden @ X37 @ 
% 0.60/0.77           (k5_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 @ X39 @ X38))
% 0.60/0.77          | (zip_tseitin_0 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 0.60/0.77      inference('simplify', [status(thm)], ['36'])).
% 0.60/0.77  thf('38', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.77         ((r2_hidden @ X7 @ 
% 0.60/0.77           (k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.60/0.77          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.60/0.77      inference('sup+', [status(thm)], ['35', '37'])).
% 0.60/0.77  thf('39', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.77         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.60/0.77          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3))),
% 0.60/0.77      inference('sup+', [status(thm)], ['34', '38'])).
% 0.60/0.77  thf('40', plain,
% 0.60/0.77      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.60/0.77         X35 : $i]:
% 0.60/0.77         (((X29) != (X28))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X28))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('41', plain,
% 0.60/0.77      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.60/0.77         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X28)),
% 0.60/0.77      inference('simplify', [status(thm)], ['40'])).
% 0.60/0.77  thf('42', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.77         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.60/0.77      inference('sup-', [status(thm)], ['39', '41'])).
% 0.60/0.77  thf('43', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.77         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['33', '42'])).
% 0.60/0.77  thf('44', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['32', '43'])).
% 0.60/0.77  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['31', '44'])).
% 0.60/0.77  thf(t14_funct_1, conjecture,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.77       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.60/0.77         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.60/0.77  thf(zf_stmt_3, negated_conjecture,
% 0.60/0.77    (~( ![A:$i,B:$i]:
% 0.60/0.77        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.77          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.60/0.77            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.60/0.77    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.60/0.77  thf('46', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('47', plain,
% 0.60/0.77      (![X55 : $i, X56 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X55 @ (k1_relat_1 @ X56))
% 0.60/0.77          | (r2_hidden @ (k1_funct_1 @ X56 @ X55) @ (k2_relat_1 @ X56))
% 0.60/0.77          | ~ (v1_funct_1 @ X56)
% 0.60/0.77          | ~ (v1_relat_1 @ X56))),
% 0.60/0.77      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.60/0.77  thf('48', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.60/0.77          | ~ (v1_relat_1 @ sk_B)
% 0.60/0.77          | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['46', '47'])).
% 0.60/0.77  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('51', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.60/0.77          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.60/0.77  thf('52', plain,
% 0.60/0.77      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['45', '51'])).
% 0.60/0.77  thf('53', plain,
% 0.60/0.77      (![X49 : $i, X51 : $i, X52 : $i]:
% 0.60/0.77         (((X51) != (k2_relat_1 @ X49))
% 0.60/0.77          | ((X52) = (k1_funct_1 @ X49 @ (sk_D_1 @ X52 @ X49)))
% 0.60/0.77          | ~ (r2_hidden @ X52 @ X51)
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (v1_relat_1 @ X49))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.77  thf('54', plain,
% 0.60/0.77      (![X49 : $i, X52 : $i]:
% 0.60/0.77         (~ (v1_relat_1 @ X49)
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (r2_hidden @ X52 @ (k2_relat_1 @ X49))
% 0.60/0.77          | ((X52) = (k1_funct_1 @ X49 @ (sk_D_1 @ X52 @ X49))))),
% 0.60/0.77      inference('simplify', [status(thm)], ['53'])).
% 0.60/0.77  thf('55', plain,
% 0.60/0.77      ((((k1_funct_1 @ sk_B @ sk_A)
% 0.60/0.77          = (k1_funct_1 @ sk_B @ (sk_D_1 @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B)))
% 0.60/0.77        | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['52', '54'])).
% 0.60/0.77  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('58', plain,
% 0.60/0.77      (((k1_funct_1 @ sk_B @ sk_A)
% 0.60/0.77         = (k1_funct_1 @ sk_B @ (sk_D_1 @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B)))),
% 0.60/0.77      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.60/0.77  thf('59', plain,
% 0.60/0.77      (![X48 : $i, X49 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X48 @ X49) @ X48)
% 0.60/0.77          | ((sk_C @ X48 @ X49) = (k1_funct_1 @ X49 @ (sk_D @ X48 @ X49)))
% 0.60/0.77          | ((X48) = (k2_relat_1 @ X49))
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (v1_relat_1 @ X49))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.77  thf('60', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('61', plain,
% 0.60/0.77      (![X48 : $i, X49 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X48 @ X49) @ X48)
% 0.60/0.77          | (r2_hidden @ (sk_D @ X48 @ X49) @ (k1_relat_1 @ X49))
% 0.60/0.77          | ((X48) = (k2_relat_1 @ X49))
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (v1_relat_1 @ X49))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.77  thf('62', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_D @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.60/0.77          | ~ (v1_relat_1 @ sk_B)
% 0.60/0.77          | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['60', '61'])).
% 0.60/0.77  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('65', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_D @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.60/0.77      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.60/0.77  thf('66', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.60/0.77          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.60/0.77  thf('67', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ X0)
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_D @ X0 @ sk_B)) @ 
% 0.60/0.77             (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['65', '66'])).
% 0.60/0.77  thf('68', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_B))
% 0.60/0.77          | ~ (v1_relat_1 @ sk_B)
% 0.60/0.77          | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ X0)
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['59', '67'])).
% 0.60/0.77  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('70', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('71', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ X0)
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.60/0.77      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.60/0.77  thf('72', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ X0)
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['71'])).
% 0.60/0.77  thf('73', plain,
% 0.60/0.77      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.60/0.77         (~ (r2_hidden @ (sk_C @ X48 @ X49) @ X48)
% 0.60/0.77          | ((sk_C @ X48 @ X49) != (k1_funct_1 @ X49 @ X50))
% 0.60/0.77          | ~ (r2_hidden @ X50 @ (k1_relat_1 @ X49))
% 0.60/0.77          | ((X48) = (k2_relat_1 @ X49))
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (v1_relat_1 @ X49))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.77  thf('74', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ~ (v1_relat_1 @ sk_B)
% 0.60/0.77          | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B))
% 0.60/0.77          | ((sk_C @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ X1)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['72', '73'])).
% 0.60/0.77  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('77', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('78', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A))
% 0.60/0.77          | ((sk_C @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ X1)))),
% 0.60/0.77      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.60/0.77  thf('79', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (((sk_C @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ X1))
% 0.60/0.77          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A))
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['78'])).
% 0.60/0.77  thf('80', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (((sk_C @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ sk_A))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ~ (r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.77               (k1_tarski @ sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['58', '79'])).
% 0.60/0.77  thf('81', plain,
% 0.60/0.77      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['45', '51'])).
% 0.60/0.77  thf('82', plain,
% 0.60/0.77      (![X49 : $i, X51 : $i, X52 : $i]:
% 0.60/0.77         (((X51) != (k2_relat_1 @ X49))
% 0.60/0.77          | (r2_hidden @ (sk_D_1 @ X52 @ X49) @ (k1_relat_1 @ X49))
% 0.60/0.77          | ~ (r2_hidden @ X52 @ X51)
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (v1_relat_1 @ X49))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.77  thf('83', plain,
% 0.60/0.77      (![X49 : $i, X52 : $i]:
% 0.60/0.77         (~ (v1_relat_1 @ X49)
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (r2_hidden @ X52 @ (k2_relat_1 @ X49))
% 0.60/0.77          | (r2_hidden @ (sk_D_1 @ X52 @ X49) @ (k1_relat_1 @ X49)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['82'])).
% 0.60/0.77  thf('84', plain,
% 0.60/0.77      (((r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.77         (k1_relat_1 @ sk_B))
% 0.60/0.77        | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['81', '83'])).
% 0.60/0.77  thf('85', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('86', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('87', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('88', plain,
% 0.60/0.77      ((r2_hidden @ (sk_D_1 @ (k1_funct_1 @ sk_B @ sk_A) @ sk_B) @ 
% 0.60/0.77        (k1_tarski @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.60/0.77  thf('89', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (((sk_C @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ sk_A))
% 0.60/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((X0) = (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('demod', [status(thm)], ['80', '88'])).
% 0.60/0.77  thf('90', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (((X0) != (k1_funct_1 @ sk_B @ sk_A))
% 0.60/0.77          | (r2_hidden @ (sk_C @ (k1_tarski @ X0) @ sk_B) @ (k2_relat_1 @ sk_B))
% 0.60/0.77          | ~ (v1_relat_1 @ sk_B)
% 0.60/0.77          | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ (k2_tarski @ X0 @ X0) @ sk_B) @ 
% 0.60/0.77             (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['30', '89'])).
% 0.60/0.77  thf('91', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('92', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('93', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (((X0) != (k1_funct_1 @ sk_B @ sk_A))
% 0.60/0.77          | (r2_hidden @ (sk_C @ (k1_tarski @ X0) @ sk_B) @ (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | (r2_hidden @ (sk_C @ (k2_tarski @ X0 @ X0) @ sk_B) @ 
% 0.60/0.77             (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.60/0.77  thf('94', plain,
% 0.60/0.77      (((r2_hidden @ 
% 0.60/0.77         (sk_C @ 
% 0.60/0.77          (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)) @ 
% 0.60/0.77          sk_B) @ 
% 0.60/0.77         (k2_relat_1 @ sk_B))
% 0.60/0.77        | ((k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.60/0.77            = (k2_relat_1 @ sk_B))
% 0.60/0.77        | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.60/0.77        | (r2_hidden @ 
% 0.60/0.77           (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77           (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['93'])).
% 0.60/0.77  thf('95', plain,
% 0.60/0.77      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('96', plain,
% 0.60/0.77      (((r2_hidden @ 
% 0.60/0.77         (sk_C @ 
% 0.60/0.77          (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)) @ 
% 0.60/0.77          sk_B) @ 
% 0.60/0.77         (k2_relat_1 @ sk_B))
% 0.60/0.77        | ((k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.60/0.77            = (k2_relat_1 @ sk_B))
% 0.60/0.77        | (r2_hidden @ 
% 0.60/0.77           (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77           (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 0.60/0.77  thf('97', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.77  thf('98', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.77  thf('99', plain,
% 0.60/0.77      (((r2_hidden @ 
% 0.60/0.77         (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77         (k2_relat_1 @ sk_B))
% 0.60/0.77        | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.60/0.77        | (r2_hidden @ 
% 0.60/0.77           (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77           (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.60/0.77  thf('100', plain,
% 0.60/0.77      ((((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.60/0.77        | (r2_hidden @ 
% 0.60/0.77           (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77           (k2_relat_1 @ sk_B)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['99'])).
% 0.60/0.77  thf('101', plain,
% 0.60/0.77      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('102', plain,
% 0.60/0.77      ((r2_hidden @ (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77        (k2_relat_1 @ sk_B))),
% 0.60/0.77      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.60/0.77  thf('103', plain,
% 0.60/0.77      (![X49 : $i, X52 : $i]:
% 0.60/0.77         (~ (v1_relat_1 @ X49)
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (r2_hidden @ X52 @ (k2_relat_1 @ X49))
% 0.60/0.77          | ((X52) = (k1_funct_1 @ X49 @ (sk_D_1 @ X52 @ X49))))),
% 0.60/0.77      inference('simplify', [status(thm)], ['53'])).
% 0.60/0.77  thf('104', plain,
% 0.60/0.77      ((((sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.60/0.77          = (k1_funct_1 @ sk_B @ 
% 0.60/0.77             (sk_D_1 @ 
% 0.60/0.77              (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ sk_B)))
% 0.60/0.77        | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['102', '103'])).
% 0.60/0.77  thf('105', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('106', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('107', plain,
% 0.60/0.77      (((sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.60/0.77         = (k1_funct_1 @ sk_B @ 
% 0.60/0.77            (sk_D_1 @ 
% 0.60/0.77             (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ sk_B)))),
% 0.60/0.77      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.60/0.77  thf('108', plain,
% 0.60/0.77      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 0.60/0.77         X36 : $i]:
% 0.60/0.77         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.60/0.77          | ((X29) = (X30))
% 0.60/0.77          | ((X29) = (X31))
% 0.60/0.77          | ((X29) = (X32))
% 0.60/0.77          | ((X29) = (X33))
% 0.60/0.77          | ((X29) = (X34))
% 0.60/0.77          | ((X29) = (X35))
% 0.60/0.77          | ((X29) = (X36)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('109', plain,
% 0.60/0.77      ((r2_hidden @ (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77        (k2_relat_1 @ sk_B))),
% 0.60/0.77      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.60/0.77  thf('110', plain,
% 0.60/0.77      (![X49 : $i, X52 : $i]:
% 0.60/0.77         (~ (v1_relat_1 @ X49)
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (r2_hidden @ X52 @ (k2_relat_1 @ X49))
% 0.60/0.77          | (r2_hidden @ (sk_D_1 @ X52 @ X49) @ (k1_relat_1 @ X49)))),
% 0.60/0.77      inference('simplify', [status(thm)], ['82'])).
% 0.60/0.77  thf('111', plain,
% 0.60/0.77      (((r2_hidden @ 
% 0.60/0.77         (sk_D_1 @ (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77          sk_B) @ 
% 0.60/0.77         (k1_relat_1 @ sk_B))
% 0.60/0.77        | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['109', '110'])).
% 0.60/0.77  thf('112', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('113', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('114', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('115', plain,
% 0.60/0.77      ((r2_hidden @ 
% 0.60/0.77        (sk_D_1 @ (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77         sk_B) @ 
% 0.60/0.77        (k1_tarski @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.60/0.77  thf('116', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.60/0.77          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['9', '25'])).
% 0.60/0.77  thf('117', plain,
% 0.60/0.77      (~ (zip_tseitin_0 @ 
% 0.60/0.77          (sk_D_1 @ (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77           sk_B) @ 
% 0.60/0.77          sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A)),
% 0.60/0.77      inference('sup-', [status(thm)], ['115', '116'])).
% 0.60/0.77  thf('118', plain,
% 0.60/0.77      ((((sk_D_1 @ (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77          sk_B) = (sk_A))
% 0.60/0.77        | ((sk_D_1 @ 
% 0.60/0.77            (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ sk_B)
% 0.60/0.77            = (sk_A))
% 0.60/0.77        | ((sk_D_1 @ 
% 0.60/0.77            (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ sk_B)
% 0.60/0.77            = (sk_A))
% 0.60/0.77        | ((sk_D_1 @ 
% 0.60/0.77            (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ sk_B)
% 0.60/0.77            = (sk_A))
% 0.60/0.77        | ((sk_D_1 @ 
% 0.60/0.77            (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ sk_B)
% 0.60/0.77            = (sk_A))
% 0.60/0.77        | ((sk_D_1 @ 
% 0.60/0.77            (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ sk_B)
% 0.60/0.77            = (sk_A))
% 0.60/0.77        | ((sk_D_1 @ 
% 0.60/0.77            (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ sk_B)
% 0.60/0.77            = (sk_A)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['108', '117'])).
% 0.60/0.77  thf('119', plain,
% 0.60/0.77      (((sk_D_1 @ (sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.60/0.77         sk_B) = (sk_A))),
% 0.60/0.77      inference('simplify', [status(thm)], ['118'])).
% 0.60/0.77  thf('120', plain,
% 0.60/0.77      (((sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.60/0.77         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['107', '119'])).
% 0.60/0.77  thf('121', plain,
% 0.60/0.77      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.60/0.77         (~ (r2_hidden @ (sk_C @ X48 @ X49) @ X48)
% 0.60/0.77          | ((sk_C @ X48 @ X49) != (k1_funct_1 @ X49 @ X50))
% 0.60/0.77          | ~ (r2_hidden @ X50 @ (k1_relat_1 @ X49))
% 0.60/0.77          | ((X48) = (k2_relat_1 @ X49))
% 0.60/0.77          | ~ (v1_funct_1 @ X49)
% 0.60/0.77          | ~ (v1_relat_1 @ X49))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.77  thf('122', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.60/0.77             (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.60/0.77          | ~ (v1_relat_1 @ sk_B)
% 0.60/0.77          | ~ (v1_funct_1 @ sk_B)
% 0.60/0.77          | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.60/0.77          | ((sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.60/0.77              != (k1_funct_1 @ sk_B @ X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['120', '121'])).
% 0.60/0.77  thf('123', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['31', '44'])).
% 0.60/0.77  thf('124', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('125', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('126', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('127', plain,
% 0.60/0.77      (((sk_C @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.60/0.77         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['107', '119'])).
% 0.60/0.77  thf('128', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.60/0.77          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.60/0.77          | ((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ X0)))),
% 0.60/0.77      inference('demod', [status(thm)],
% 0.60/0.77                ['122', '123', '124', '125', '126', '127'])).
% 0.60/0.77  thf('129', plain,
% 0.60/0.77      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.77  thf('130', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.60/0.77          | ((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ X0)))),
% 0.60/0.77      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 0.60/0.77  thf('131', plain, (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 0.60/0.77      inference('eq_res', [status(thm)], ['130'])).
% 0.60/0.77  thf('132', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['31', '44'])).
% 0.60/0.77  thf('133', plain, ($false), inference('demod', [status(thm)], ['131', '132'])).
% 0.60/0.77  
% 0.60/0.77  % SZS output end Refutation
% 0.60/0.77  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
