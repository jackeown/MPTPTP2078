%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9BMo4taja6

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:24 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 439 expanded)
%              Number of leaves         :   26 ( 132 expanded)
%              Depth                    :   25
%              Number of atoms          :  901 (5576 expanded)
%              Number of equality atoms :  118 ( 744 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X23 @ X22 ) @ X22 )
      | ( X22
        = ( k1_tarski @ X23 ) ) ) ),
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

thf('4',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( X28
       != ( k2_relat_1 @ X26 ) )
      | ( r2_hidden @ ( sk_D_1 @ X29 @ X26 ) @ ( k1_relat_1 @ X26 ) )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('5',plain,(
    ! [X26: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r2_hidden @ X29 @ ( k2_relat_1 @ X26 ) )
      | ( r2_hidden @ ( sk_D_1 @ X29 @ X26 ) @ ( k1_relat_1 @ X26 ) ) ) ),
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
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X23 @ X22 ) @ X22 )
      | ( X22
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('21',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( X28
       != ( k2_relat_1 @ X26 ) )
      | ( X29
        = ( k1_funct_1 @ X26 @ ( sk_D_1 @ X29 @ X26 ) ) )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('22',plain,(
    ! [X26: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r2_hidden @ X29 @ ( k2_relat_1 @ X26 ) )
      | ( X29
        = ( k1_funct_1 @ X26 @ ( sk_D_1 @ X29 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
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
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
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
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( ( sk_C @ X23 @ X22 )
       != X23 )
      | ( X22
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('30',plain,(
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
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X26: $i,X28: $i,X30: $i,X31: $i] :
      ( ( X28
       != ( k2_relat_1 @ X26 ) )
      | ( r2_hidden @ X30 @ X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X26 ) )
      | ( X30
       != ( k1_funct_1 @ X26 @ X31 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('53',plain,(
    ! [X26: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X26 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X26 @ X31 ) @ ( k2_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('60',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('62',plain,(
    r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('66',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( k1_funct_1 @ k1_xboole_0 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['66','67'])).

thf('75',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['41','73','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9BMo4taja6
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:38:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 270 iterations in 0.206s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(t14_funct_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.46/0.66         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i]:
% 0.46/0.66        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.46/0.66            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d1_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.66           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_1, axiom,
% 0.46/0.66    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.66       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.46/0.66          | ((X1) = (X2))
% 0.46/0.66          | ((X1) = (X3))
% 0.46/0.66          | ((X1) = (X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('2', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t41_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i]:
% 0.46/0.66         (((X22) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X23 @ X22) @ X22)
% 0.46/0.66          | ((X22) = (k1_tarski @ X23)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.46/0.66  thf(d5_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.66               ( ?[D:$i]:
% 0.46/0.66                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.46/0.66                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.46/0.66         (((X28) != (k2_relat_1 @ X26))
% 0.46/0.66          | (r2_hidden @ (sk_D_1 @ X29 @ X26) @ (k1_relat_1 @ X26))
% 0.46/0.66          | ~ (r2_hidden @ X29 @ X28)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X26 : $i, X29 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X26)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (r2_hidden @ X29 @ (k2_relat_1 @ X26))
% 0.46/0.66          | (r2_hidden @ (sk_D_1 @ X29 @ X26) @ (k1_relat_1 @ X26)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 0.46/0.66          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.46/0.66             (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '5'])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.46/0.66           (k1_tarski @ sk_A))
% 0.46/0.66          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.66          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['2', '6'])).
% 0.46/0.66  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.46/0.66           (k1_tarski @ sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.46/0.66  thf(t69_enumset1, axiom,
% 0.46/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf(t70_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_3, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X10 @ X9)
% 0.46/0.66          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.46/0.66          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.46/0.66          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['12', '14'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ 
% 0.46/0.66               (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ sk_A @ 
% 0.46/0.66               sk_A @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['10', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.46/0.66          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.46/0.66          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i]:
% 0.46/0.66         (((X22) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X23 @ X22) @ X22)
% 0.46/0.66          | ((X22) = (k1_tarski @ X23)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.46/0.66         (((X28) != (k2_relat_1 @ X26))
% 0.46/0.66          | ((X29) = (k1_funct_1 @ X26 @ (sk_D_1 @ X29 @ X26)))
% 0.46/0.66          | ~ (r2_hidden @ X29 @ X28)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X26 : $i, X29 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X26)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (r2_hidden @ X29 @ (k2_relat_1 @ X26))
% 0.46/0.66          | ((X29) = (k1_funct_1 @ X26 @ (sk_D_1 @ X29 @ X26))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['21'])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 0.46/0.66          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.66          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.66              = (k1_funct_1 @ X0 @ 
% 0.46/0.66                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['20', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.66          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['19', '23'])).
% 0.46/0.66  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i]:
% 0.46/0.66         (((X22) = (k1_xboole_0))
% 0.46/0.66          | ((sk_C @ X23 @ X22) != (X23))
% 0.46/0.66          | ((X22) = (k1_tarski @ X23)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      ((((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.46/0.66        | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('33', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '33'])).
% 0.46/0.66  thf('35', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf(t64_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.66           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.66         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X24 : $i]:
% 0.46/0.66         (((k2_relat_1 @ X24) != (k1_xboole_0))
% 0.46/0.66          | ((X24) = (k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ X24))),
% 0.46/0.66      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_B)
% 0.46/0.66        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['34', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.46/0.66          | (r2_hidden @ X5 @ X9)
% 0.46/0.66          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.66         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.46/0.66          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.46/0.66      inference('simplify', [status(thm)], ['44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.66          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['43', '45'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.66         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.46/0.66      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['46', '48'])).
% 0.46/0.66  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['42', '49'])).
% 0.46/0.66  thf('51', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X26 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         (((X28) != (k2_relat_1 @ X26))
% 0.46/0.66          | (r2_hidden @ X30 @ X28)
% 0.46/0.66          | ~ (r2_hidden @ X31 @ (k1_relat_1 @ X26))
% 0.46/0.66          | ((X30) != (k1_funct_1 @ X26 @ X31))
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X26 : $i, X31 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X26)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (r2_hidden @ X31 @ (k1_relat_1 @ X26))
% 0.46/0.66          | (r2_hidden @ (k1_funct_1 @ X26 @ X31) @ (k2_relat_1 @ X26)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.66          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))
% 0.46/0.66          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.66          | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '53'])).
% 0.46/0.66  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.66          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['50', '57'])).
% 0.46/0.66  thf('59', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('60', plain, ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.66  thf('61', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.46/0.66          | ((X1) = (X2))
% 0.46/0.66          | ((X1) = (X3))
% 0.46/0.66          | ((X1) = (X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('64', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('65', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.66  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf(t60_relat_1, axiom,
% 0.46/0.66    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.66     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.66  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.66  thf('68', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '15'])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.46/0.66          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (sk_A))
% 0.46/0.66          | ((X0) = (sk_A))
% 0.46/0.66          | ((X0) = (sk_A))
% 0.46/0.66          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['63', '70'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['71'])).
% 0.46/0.66  thf('73', plain, (((k1_funct_1 @ k1_xboole_0 @ sk_A) = (sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['62', '72'])).
% 0.46/0.66  thf('74', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf('75', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['41', '73', '74'])).
% 0.46/0.66  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
