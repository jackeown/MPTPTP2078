%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.olutafyXef

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:26 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 118 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   20
%              Number of atoms          :  924 (1270 expanded)
%              Number of equality atoms :  112 ( 158 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 )
      | ( X29 = X33 )
      | ( X29 = X34 ) ) ),
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

thf('1',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X27 @ X26 ) @ X26 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

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
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( X48
       != ( k2_relat_1 @ X46 ) )
      | ( r2_hidden @ ( sk_D_1 @ X49 @ X46 ) @ ( k1_relat_1 @ X46 ) )
      | ~ ( r2_hidden @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('4',plain,(
    ! [X46: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( r2_hidden @ X49 @ ( k2_relat_1 @ X46 ) )
      | ( r2_hidden @ ( sk_D_1 @ X49 @ X46 ) @ ( k1_relat_1 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ~ ( zip_tseitin_0 @ X42 @ X36 @ X37 @ X38 @ X39 @ X40 )
      | ( X41
       != ( k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X36 @ X37 @ X38 @ X39 @ X40 )
      | ~ ( r2_hidden @ X42 @ ( k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36 ) ) ) ),
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
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
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
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X27 @ X26 ) @ X26 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('24',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( X48
       != ( k2_relat_1 @ X46 ) )
      | ( X49
        = ( k1_funct_1 @ X46 @ ( sk_D_1 @ X49 @ X46 ) ) )
      | ~ ( r2_hidden @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('25',plain,(
    ! [X46: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( r2_hidden @ X49 @ ( k2_relat_1 @ X46 ) )
      | ( X49
        = ( k1_funct_1 @ X46 @ ( sk_D_1 @ X49 @ X46 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
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
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
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
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( sk_C @ X27 @ X26 )
       != X27 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('33',plain,(
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
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X44: $i] :
      ( ( ( k2_relat_1 @ X44 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X44 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('47',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      | ( r2_hidden @ X35 @ X41 )
      | ( X41
       != ( k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ X35 @ ( k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36 ) )
      | ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X28: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X28 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','54'])).

thf('56',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_zfmisc_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X22: $i] :
      ( ( k2_zfmisc_1 @ X22 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('59',plain,(
    ! [X24: $i,X25: $i] :
      ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('sup-',[status(thm)],['56','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.olutafyXef
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.60/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.82  % Solved by: fo/fo7.sh
% 0.60/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.82  % done 388 iterations in 0.370s
% 0.60/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.82  % SZS output start Refutation
% 0.60/0.82  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.60/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.82  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.60/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.60/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.82  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.60/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.82  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.60/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.82  thf(d3_enumset1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.60/0.82     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.60/0.82       ( ![G:$i]:
% 0.60/0.82         ( ( r2_hidden @ G @ F ) <=>
% 0.60/0.82           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.60/0.82                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_0, axiom,
% 0.60/0.82    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.60/0.82     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.60/0.82       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.60/0.82         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.60/0.82  thf('0', plain,
% 0.60/0.82      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.82         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.60/0.82          | ((X29) = (X30))
% 0.60/0.82          | ((X29) = (X31))
% 0.60/0.82          | ((X29) = (X32))
% 0.60/0.82          | ((X29) = (X33))
% 0.60/0.82          | ((X29) = (X34)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(t14_funct_1, conjecture,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.82       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.60/0.82         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_1, negated_conjecture,
% 0.60/0.82    (~( ![A:$i,B:$i]:
% 0.60/0.82        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.82          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.60/0.82            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.60/0.82    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.60/0.82  thf('1', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf(t41_zfmisc_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.60/0.82          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.60/0.82  thf('2', plain,
% 0.60/0.82      (![X26 : $i, X27 : $i]:
% 0.60/0.82         (((X26) = (k1_xboole_0))
% 0.60/0.82          | (r2_hidden @ (sk_C @ X27 @ X26) @ X26)
% 0.60/0.82          | ((X26) = (k1_tarski @ X27)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.60/0.82  thf(d5_funct_1, axiom,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.82       ( ![B:$i]:
% 0.60/0.82         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.60/0.82           ( ![C:$i]:
% 0.60/0.82             ( ( r2_hidden @ C @ B ) <=>
% 0.60/0.82               ( ?[D:$i]:
% 0.60/0.82                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.60/0.82                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.60/0.82  thf('3', plain,
% 0.60/0.82      (![X46 : $i, X48 : $i, X49 : $i]:
% 0.60/0.82         (((X48) != (k2_relat_1 @ X46))
% 0.60/0.82          | (r2_hidden @ (sk_D_1 @ X49 @ X46) @ (k1_relat_1 @ X46))
% 0.60/0.82          | ~ (r2_hidden @ X49 @ X48)
% 0.60/0.82          | ~ (v1_funct_1 @ X46)
% 0.60/0.82          | ~ (v1_relat_1 @ X46))),
% 0.60/0.82      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.82  thf('4', plain,
% 0.60/0.82      (![X46 : $i, X49 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X46)
% 0.60/0.82          | ~ (v1_funct_1 @ X46)
% 0.60/0.82          | ~ (r2_hidden @ X49 @ (k2_relat_1 @ X46))
% 0.60/0.82          | (r2_hidden @ (sk_D_1 @ X49 @ X46) @ (k1_relat_1 @ X46)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['3'])).
% 0.60/0.82  thf('5', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 0.60/0.82          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.60/0.82          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.60/0.82             (k1_relat_1 @ X0))
% 0.60/0.82          | ~ (v1_funct_1 @ X0)
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['2', '4'])).
% 0.60/0.82  thf('6', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.60/0.82           (k1_tarski @ sk_A))
% 0.60/0.82          | ~ (v1_relat_1 @ sk_B)
% 0.60/0.82          | ~ (v1_funct_1 @ sk_B)
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.60/0.82      inference('sup+', [status(thm)], ['1', '5'])).
% 0.60/0.82  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf('9', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.60/0.82           (k1_tarski @ sk_A))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.60/0.82      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.60/0.82  thf(t69_enumset1, axiom,
% 0.60/0.82    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.82  thf('10', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.82  thf(t70_enumset1, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.60/0.82  thf('11', plain,
% 0.60/0.82      (![X1 : $i, X2 : $i]:
% 0.60/0.82         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.60/0.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.82  thf(t71_enumset1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.60/0.82  thf('12', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.82         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.60/0.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.60/0.82  thf(t72_enumset1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.82     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.60/0.82  thf('13', plain,
% 0.60/0.82      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.82         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.60/0.82           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.60/0.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.60/0.82  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.60/0.82  thf(zf_stmt_3, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.60/0.82     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.60/0.82       ( ![G:$i]:
% 0.60/0.82         ( ( r2_hidden @ G @ F ) <=>
% 0.60/0.82           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.60/0.82  thf('14', plain,
% 0.60/0.82      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X42 @ X41)
% 0.60/0.82          | ~ (zip_tseitin_0 @ X42 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.60/0.82          | ((X41) != (k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.82  thf('15', plain,
% 0.60/0.82      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.60/0.82         (~ (zip_tseitin_0 @ X42 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.60/0.82          | ~ (r2_hidden @ X42 @ (k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['14'])).
% 0.60/0.82  thf('16', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.60/0.82          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.60/0.82      inference('sup-', [status(thm)], ['13', '15'])).
% 0.60/0.82  thf('17', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.60/0.82          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2))),
% 0.60/0.82      inference('sup-', [status(thm)], ['12', '16'])).
% 0.60/0.82  thf('18', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.60/0.82          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['11', '17'])).
% 0.60/0.82  thf('19', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.60/0.82          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['10', '18'])).
% 0.60/0.82  thf('20', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ~ (zip_tseitin_0 @ 
% 0.60/0.82               (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ sk_A @ 
% 0.60/0.82               sk_A @ sk_A @ sk_A @ sk_A))),
% 0.60/0.82      inference('sup-', [status(thm)], ['9', '19'])).
% 0.60/0.82  thf('21', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.60/0.82          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.60/0.82          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.60/0.82          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.60/0.82          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['0', '20'])).
% 0.60/0.82  thf('22', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['21'])).
% 0.60/0.82  thf('23', plain,
% 0.60/0.82      (![X26 : $i, X27 : $i]:
% 0.60/0.82         (((X26) = (k1_xboole_0))
% 0.60/0.82          | (r2_hidden @ (sk_C @ X27 @ X26) @ X26)
% 0.60/0.82          | ((X26) = (k1_tarski @ X27)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.60/0.82  thf('24', plain,
% 0.60/0.82      (![X46 : $i, X48 : $i, X49 : $i]:
% 0.60/0.82         (((X48) != (k2_relat_1 @ X46))
% 0.60/0.82          | ((X49) = (k1_funct_1 @ X46 @ (sk_D_1 @ X49 @ X46)))
% 0.60/0.82          | ~ (r2_hidden @ X49 @ X48)
% 0.60/0.82          | ~ (v1_funct_1 @ X46)
% 0.60/0.82          | ~ (v1_relat_1 @ X46))),
% 0.60/0.82      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.82  thf('25', plain,
% 0.60/0.82      (![X46 : $i, X49 : $i]:
% 0.60/0.82         (~ (v1_relat_1 @ X46)
% 0.60/0.82          | ~ (v1_funct_1 @ X46)
% 0.60/0.82          | ~ (r2_hidden @ X49 @ (k2_relat_1 @ X46))
% 0.60/0.82          | ((X49) = (k1_funct_1 @ X46 @ (sk_D_1 @ X49 @ X46))))),
% 0.60/0.82      inference('simplify', [status(thm)], ['24'])).
% 0.60/0.82  thf('26', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 0.60/0.82          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.60/0.82          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.60/0.82              = (k1_funct_1 @ X0 @ 
% 0.60/0.82                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 0.60/0.82          | ~ (v1_funct_1 @ X0)
% 0.60/0.82          | ~ (v1_relat_1 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['23', '25'])).
% 0.60/0.82  thf('27', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.60/0.82          | ~ (v1_relat_1 @ sk_B)
% 0.60/0.82          | ~ (v1_funct_1 @ sk_B)
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.60/0.82      inference('sup+', [status(thm)], ['22', '26'])).
% 0.60/0.82  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf('30', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.60/0.82      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.60/0.82  thf('31', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['30'])).
% 0.60/0.82  thf('32', plain,
% 0.60/0.82      (![X26 : $i, X27 : $i]:
% 0.60/0.82         (((X26) = (k1_xboole_0))
% 0.60/0.82          | ((sk_C @ X27 @ X26) != (X27))
% 0.60/0.82          | ((X26) = (k1_tarski @ X27)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.60/0.82  thf('33', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.60/0.82          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.82  thf('34', plain,
% 0.60/0.82      ((((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.60/0.82        | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['33'])).
% 0.60/0.82  thf('35', plain,
% 0.60/0.82      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf('36', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.60/0.82      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.60/0.82  thf(t65_relat_1, axiom,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ A ) =>
% 0.60/0.82       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.60/0.82         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.82  thf('37', plain,
% 0.60/0.82      (![X44 : $i]:
% 0.60/0.82         (((k2_relat_1 @ X44) != (k1_xboole_0))
% 0.60/0.82          | ((k1_relat_1 @ X44) = (k1_xboole_0))
% 0.60/0.82          | ~ (v1_relat_1 @ X44))),
% 0.60/0.82      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.60/0.82  thf('38', plain,
% 0.60/0.82      ((((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.82        | ~ (v1_relat_1 @ sk_B)
% 0.60/0.82        | ((k1_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.82  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf('40', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf('41', plain,
% 0.60/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.60/0.82      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.60/0.82  thf('42', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.60/0.82      inference('simplify', [status(thm)], ['41'])).
% 0.60/0.82  thf('43', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.60/0.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.82  thf('44', plain,
% 0.60/0.82      (![X1 : $i, X2 : $i]:
% 0.60/0.82         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.60/0.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.82  thf('45', plain,
% 0.60/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.82         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.60/0.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.60/0.82  thf('46', plain,
% 0.60/0.82      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.82         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.60/0.82           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.60/0.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.60/0.82  thf('47', plain,
% 0.60/0.82      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.60/0.82         ((zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.60/0.82          | (r2_hidden @ X35 @ X41)
% 0.60/0.82          | ((X41) != (k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.82  thf('48', plain,
% 0.60/0.82      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.60/0.82         ((r2_hidden @ X35 @ (k3_enumset1 @ X40 @ X39 @ X38 @ X37 @ X36))
% 0.60/0.82          | (zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 0.60/0.82      inference('simplify', [status(thm)], ['47'])).
% 0.60/0.82  thf('49', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.82         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.60/0.82          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.60/0.82      inference('sup+', [status(thm)], ['46', '48'])).
% 0.60/0.82  thf('50', plain,
% 0.60/0.82      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.60/0.82         (((X29) != (X28))
% 0.60/0.82          | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 @ X33 @ X28))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('51', plain,
% 0.60/0.82      (![X28 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.60/0.82         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X32 @ X33 @ X28)),
% 0.60/0.82      inference('simplify', [status(thm)], ['50'])).
% 0.60/0.82  thf('52', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.82         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.60/0.82      inference('sup-', [status(thm)], ['49', '51'])).
% 0.60/0.82  thf('53', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.82         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.60/0.82      inference('sup+', [status(thm)], ['45', '52'])).
% 0.60/0.82  thf('54', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.60/0.82      inference('sup+', [status(thm)], ['44', '53'])).
% 0.60/0.82  thf('55', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.60/0.82      inference('sup+', [status(thm)], ['43', '54'])).
% 0.60/0.82  thf('56', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.60/0.82      inference('sup+', [status(thm)], ['42', '55'])).
% 0.60/0.82  thf(t113_zfmisc_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.60/0.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.82  thf('57', plain,
% 0.60/0.82      (![X22 : $i, X23 : $i]:
% 0.60/0.82         (((k2_zfmisc_1 @ X22 @ X23) = (k1_xboole_0))
% 0.60/0.82          | ((X23) != (k1_xboole_0)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.82  thf('58', plain,
% 0.60/0.82      (![X22 : $i]: ((k2_zfmisc_1 @ X22 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.82      inference('simplify', [status(thm)], ['57'])).
% 0.60/0.82  thf(t152_zfmisc_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.60/0.82  thf('59', plain,
% 0.60/0.82      (![X24 : $i, X25 : $i]: ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X24 @ X25))),
% 0.60/0.82      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.60/0.82  thf('60', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.60/0.82      inference('sup-', [status(thm)], ['58', '59'])).
% 0.60/0.82  thf('61', plain, ($false), inference('sup-', [status(thm)], ['56', '60'])).
% 0.60/0.82  
% 0.60/0.82  % SZS output end Refutation
% 0.60/0.82  
% 0.60/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
