%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4FeuA1Tx2Q

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:21 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 292 expanded)
%              Number of leaves         :   34 (  98 expanded)
%              Depth                    :   24
%              Number of atoms          : 1258 (2841 expanded)
%              Number of equality atoms :  113 ( 273 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X1 @ X1 @ X1 )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = X0 )
      | ( X2 = X0 )
      | ( X2 = X1 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ X0 @ X0 )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 )
      | ( X1 = X0 ) ) ),
    inference(condensation,[status(thm)],['32'])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X27 @ X26 ) @ X26 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('35',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('39',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k11_relat_1 @ X32 @ X33 )
        = k1_xboole_0 )
      | ( r2_hidden @ X33 @ ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('49',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( X39
       != ( k2_relat_1 @ X37 ) )
      | ( r2_hidden @ ( sk_D_1 @ X40 @ X37 ) @ ( k1_relat_1 @ X37 ) )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('50',plain,(
    ! [X37: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( r2_hidden @ X40 @ ( k2_relat_1 @ X37 ) )
      | ( r2_hidden @ ( sk_D_1 @ X40 @ X37 ) @ ( k1_relat_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X32 ) )
      | ( ( k11_relat_1 @ X32 @ X33 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( X39
       != ( k2_relat_1 @ X37 ) )
      | ( X40
        = ( k1_funct_1 @ X37 @ ( sk_D_1 @ X40 @ X37 ) ) )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('62',plain,(
    ! [X37: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( r2_hidden @ X40 @ ( k2_relat_1 @ X37 ) )
      | ( X40
        = ( k1_funct_1 @ X37 @ ( sk_D_1 @ X40 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ X32 ) )
      | ( ( k11_relat_1 @ X32 @ X33 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','81'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('83',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k11_relat_1 @ X28 @ X29 )
        = ( k9_relat_1 @ X28 @ ( k1_tarski @ X29 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('84',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('89',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ( ( k7_relat_1 @ X34 @ X35 )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( ( k7_relat_1 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['87','92'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('94',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) )
        = ( k9_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('95',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['83','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['82','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['75','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','104'])).

thf('106',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( sk_C_1 @ X27 @ X26 )
       != X27 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('110',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['82','100'])).

thf('111',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['108','109','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4FeuA1Tx2Q
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.73/1.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.73/1.91  % Solved by: fo/fo7.sh
% 1.73/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.73/1.91  % done 1789 iterations in 1.446s
% 1.73/1.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.73/1.91  % SZS output start Refutation
% 1.73/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.73/1.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.73/1.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.73/1.91  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.73/1.91  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.73/1.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.73/1.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.73/1.91  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.73/1.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.73/1.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.73/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.73/1.91  thf(sk_B_type, type, sk_B: $i).
% 1.73/1.91  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.73/1.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.73/1.91  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.73/1.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.73/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.73/1.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.73/1.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.73/1.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.73/1.91  thf(d1_enumset1, axiom,
% 1.73/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.73/1.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.73/1.91       ( ![E:$i]:
% 1.73/1.91         ( ( r2_hidden @ E @ D ) <=>
% 1.73/1.91           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.73/1.91  thf(zf_stmt_0, axiom,
% 1.73/1.91    (![E:$i,C:$i,B:$i,A:$i]:
% 1.73/1.91     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.73/1.91       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.73/1.91  thf('0', plain,
% 1.73/1.91      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.73/1.91         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 1.73/1.91          | ((X5) = (X6))
% 1.73/1.91          | ((X5) = (X7))
% 1.73/1.91          | ((X5) = (X8)))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.91  thf(t70_enumset1, axiom,
% 1.73/1.91    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.73/1.91  thf('1', plain,
% 1.73/1.91      (![X17 : $i, X18 : $i]:
% 1.73/1.91         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.73/1.91      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.73/1.91  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.73/1.91  thf(zf_stmt_2, axiom,
% 1.73/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.73/1.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.73/1.91       ( ![E:$i]:
% 1.73/1.91         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.73/1.91  thf('2', plain,
% 1.73/1.91      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.73/1.91         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 1.73/1.91          | (r2_hidden @ X9 @ X13)
% 1.73/1.91          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.73/1.91  thf('3', plain,
% 1.73/1.91      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.73/1.91         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 1.73/1.91          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 1.73/1.91      inference('simplify', [status(thm)], ['2'])).
% 1.73/1.91  thf('4', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.73/1.91          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.73/1.91      inference('sup+', [status(thm)], ['1', '3'])).
% 1.73/1.91  thf(t69_enumset1, axiom,
% 1.73/1.91    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.73/1.91  thf('5', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.73/1.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.73/1.91  thf('6', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.73/1.91          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.73/1.91      inference('sup+', [status(thm)], ['1', '3'])).
% 1.73/1.91  thf('7', plain,
% 1.73/1.91      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.73/1.91         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.91  thf('8', plain,
% 1.73/1.91      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 1.73/1.91      inference('simplify', [status(thm)], ['7'])).
% 1.73/1.91  thf('9', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.73/1.91      inference('sup-', [status(thm)], ['6', '8'])).
% 1.73/1.91  thf('10', plain,
% 1.73/1.91      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.73/1.91         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 1.73/1.91          | ((X5) = (X6))
% 1.73/1.91          | ((X5) = (X7))
% 1.73/1.91          | ((X5) = (X8)))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.91  thf(d3_tarski, axiom,
% 1.73/1.91    (![A:$i,B:$i]:
% 1.73/1.91     ( ( r1_tarski @ A @ B ) <=>
% 1.73/1.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.73/1.91  thf('11', plain,
% 1.73/1.91      (![X1 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('12', plain,
% 1.73/1.91      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.73/1.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.73/1.91  thf('13', plain,
% 1.73/1.91      (![X17 : $i, X18 : $i]:
% 1.73/1.91         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.73/1.91      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.73/1.91  thf('14', plain,
% 1.73/1.91      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.73/1.91         (~ (r2_hidden @ X14 @ X13)
% 1.73/1.91          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 1.73/1.91          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.73/1.91  thf('15', plain,
% 1.73/1.91      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 1.73/1.91         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 1.73/1.91          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.73/1.91      inference('simplify', [status(thm)], ['14'])).
% 1.73/1.91  thf('16', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.73/1.91          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.73/1.91      inference('sup-', [status(thm)], ['13', '15'])).
% 1.73/1.91  thf('17', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.73/1.91          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.73/1.91      inference('sup-', [status(thm)], ['12', '16'])).
% 1.73/1.91  thf('18', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.73/1.91          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.73/1.91      inference('sup-', [status(thm)], ['11', '17'])).
% 1.73/1.91  thf('19', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.73/1.91          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.73/1.91          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.73/1.91          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.73/1.91      inference('sup-', [status(thm)], ['10', '18'])).
% 1.73/1.91  thf('20', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.73/1.91          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.73/1.91      inference('simplify', [status(thm)], ['19'])).
% 1.73/1.91  thf('21', plain,
% 1.73/1.91      (![X1 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('22', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (~ (r2_hidden @ X0 @ X1)
% 1.73/1.91          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.73/1.91          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.73/1.91      inference('sup-', [status(thm)], ['20', '21'])).
% 1.73/1.91  thf('23', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.73/1.91      inference('simplify', [status(thm)], ['22'])).
% 1.73/1.91  thf('24', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.73/1.91      inference('sup-', [status(thm)], ['9', '23'])).
% 1.73/1.91  thf('25', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X1))),
% 1.73/1.91      inference('sup+', [status(thm)], ['5', '24'])).
% 1.73/1.91  thf('26', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (~ (r2_hidden @ X0 @ X1)
% 1.73/1.91          | (r2_hidden @ X0 @ X2)
% 1.73/1.91          | ~ (r1_tarski @ X1 @ X2))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('27', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.73/1.91          | ~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X1)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['25', '26'])).
% 1.73/1.91  thf('28', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((zip_tseitin_0 @ X1 @ X0 @ X0 @ X0)
% 1.73/1.91          | (r2_hidden @ X1 @ (k2_tarski @ X0 @ X2)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['4', '27'])).
% 1.73/1.91  thf('29', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.73/1.91          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.73/1.91      inference('sup-', [status(thm)], ['13', '15'])).
% 1.73/1.91  thf('30', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((zip_tseitin_0 @ X2 @ X1 @ X1 @ X1)
% 1.73/1.91          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.73/1.91      inference('sup-', [status(thm)], ['28', '29'])).
% 1.73/1.91  thf('31', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (((X2) = (X0))
% 1.73/1.91          | ((X2) = (X0))
% 1.73/1.91          | ((X2) = (X1))
% 1.73/1.91          | (zip_tseitin_0 @ X2 @ X0 @ X0 @ X0))),
% 1.73/1.91      inference('sup-', [status(thm)], ['0', '30'])).
% 1.73/1.91  thf('32', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((zip_tseitin_0 @ X2 @ X0 @ X0 @ X0) | ((X2) = (X1)) | ((X2) = (X0)))),
% 1.73/1.91      inference('simplify', [status(thm)], ['31'])).
% 1.73/1.91  thf('33', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((zip_tseitin_0 @ X1 @ X0 @ X0 @ X0) | ((X1) = (X0)))),
% 1.73/1.91      inference('condensation', [status(thm)], ['32'])).
% 1.73/1.91  thf(l44_zfmisc_1, axiom,
% 1.73/1.91    (![A:$i,B:$i]:
% 1.73/1.91     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.73/1.91          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 1.73/1.91  thf('34', plain,
% 1.73/1.91      (![X26 : $i, X27 : $i]:
% 1.73/1.91         (((X26) = (k1_xboole_0))
% 1.73/1.91          | (r2_hidden @ (sk_C_1 @ X27 @ X26) @ X26)
% 1.73/1.91          | ((X26) = (k1_tarski @ X27)))),
% 1.73/1.91      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.73/1.91  thf('35', plain,
% 1.73/1.91      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.73/1.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.73/1.91  thf('36', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.73/1.91      inference('sup-', [status(thm)], ['6', '8'])).
% 1.73/1.91  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.73/1.91      inference('sup+', [status(thm)], ['35', '36'])).
% 1.73/1.91  thf('38', plain,
% 1.73/1.91      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.73/1.91         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 1.73/1.91          | ((X5) = (X6))
% 1.73/1.91          | ((X5) = (X7))
% 1.73/1.91          | ((X5) = (X8)))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.91  thf(t14_funct_1, conjecture,
% 1.73/1.91    (![A:$i,B:$i]:
% 1.73/1.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.73/1.91       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.73/1.91         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.73/1.91  thf(zf_stmt_3, negated_conjecture,
% 1.73/1.91    (~( ![A:$i,B:$i]:
% 1.73/1.91        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.73/1.91          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.73/1.91            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 1.73/1.91    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 1.73/1.91  thf('39', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.91  thf(t205_relat_1, axiom,
% 1.73/1.91    (![A:$i,B:$i]:
% 1.73/1.91     ( ( v1_relat_1 @ B ) =>
% 1.73/1.91       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 1.73/1.91         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 1.73/1.91  thf('40', plain,
% 1.73/1.91      (![X32 : $i, X33 : $i]:
% 1.73/1.91         (((k11_relat_1 @ X32 @ X33) = (k1_xboole_0))
% 1.73/1.91          | (r2_hidden @ X33 @ (k1_relat_1 @ X32))
% 1.73/1.91          | ~ (v1_relat_1 @ X32))),
% 1.73/1.91      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.73/1.91  thf('41', plain,
% 1.73/1.91      (![X0 : $i]:
% 1.73/1.91         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.73/1.91          | ~ (v1_relat_1 @ sk_B)
% 1.73/1.91          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 1.73/1.91      inference('sup+', [status(thm)], ['39', '40'])).
% 1.73/1.92  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('43', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.73/1.92          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 1.73/1.92      inference('demod', [status(thm)], ['41', '42'])).
% 1.73/1.92  thf('44', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.73/1.92          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['12', '16'])).
% 1.73/1.92  thf('45', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0))
% 1.73/1.92          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['43', '44'])).
% 1.73/1.92  thf('46', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((X0) = (sk_A))
% 1.73/1.92          | ((X0) = (sk_A))
% 1.73/1.92          | ((X0) = (sk_A))
% 1.73/1.92          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['38', '45'])).
% 1.73/1.92  thf('47', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)) | ((X0) = (sk_A)))),
% 1.73/1.92      inference('simplify', [status(thm)], ['46'])).
% 1.73/1.92  thf('48', plain,
% 1.73/1.92      (![X1 : $i, X3 : $i]:
% 1.73/1.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.92  thf(d5_funct_1, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.73/1.92           ( ![C:$i]:
% 1.73/1.92             ( ( r2_hidden @ C @ B ) <=>
% 1.73/1.92               ( ?[D:$i]:
% 1.73/1.92                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.73/1.92                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.73/1.92  thf('49', plain,
% 1.73/1.92      (![X37 : $i, X39 : $i, X40 : $i]:
% 1.73/1.92         (((X39) != (k2_relat_1 @ X37))
% 1.73/1.92          | (r2_hidden @ (sk_D_1 @ X40 @ X37) @ (k1_relat_1 @ X37))
% 1.73/1.92          | ~ (r2_hidden @ X40 @ X39)
% 1.73/1.92          | ~ (v1_funct_1 @ X37)
% 1.73/1.92          | ~ (v1_relat_1 @ X37))),
% 1.73/1.92      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.73/1.92  thf('50', plain,
% 1.73/1.92      (![X37 : $i, X40 : $i]:
% 1.73/1.92         (~ (v1_relat_1 @ X37)
% 1.73/1.92          | ~ (v1_funct_1 @ X37)
% 1.73/1.92          | ~ (r2_hidden @ X40 @ (k2_relat_1 @ X37))
% 1.73/1.92          | (r2_hidden @ (sk_D_1 @ X40 @ X37) @ (k1_relat_1 @ X37)))),
% 1.73/1.92      inference('simplify', [status(thm)], ['49'])).
% 1.73/1.92  thf('51', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.73/1.92          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.73/1.92             (k1_relat_1 @ X0))
% 1.73/1.92          | ~ (v1_funct_1 @ X0)
% 1.73/1.92          | ~ (v1_relat_1 @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['48', '50'])).
% 1.73/1.92  thf('52', plain,
% 1.73/1.92      (![X32 : $i, X33 : $i]:
% 1.73/1.92         (~ (r2_hidden @ X33 @ (k1_relat_1 @ X32))
% 1.73/1.92          | ((k11_relat_1 @ X32 @ X33) != (k1_xboole_0))
% 1.73/1.92          | ~ (v1_relat_1 @ X32))),
% 1.73/1.92      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.73/1.92  thf('53', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (~ (v1_relat_1 @ X0)
% 1.73/1.92          | ~ (v1_funct_1 @ X0)
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.73/1.92          | ~ (v1_relat_1 @ X0)
% 1.73/1.92          | ((k11_relat_1 @ X0 @ 
% 1.73/1.92              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) != (k1_xboole_0)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['51', '52'])).
% 1.73/1.92  thf('54', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (((k11_relat_1 @ X0 @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0))
% 1.73/1.92            != (k1_xboole_0))
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.73/1.92          | ~ (v1_funct_1 @ X0)
% 1.73/1.92          | ~ (v1_relat_1 @ X0))),
% 1.73/1.92      inference('simplify', [status(thm)], ['53'])).
% 1.73/1.92  thf('55', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((k1_xboole_0) != (k1_xboole_0))
% 1.73/1.92          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 1.73/1.92          | ~ (v1_relat_1 @ sk_B)
% 1.73/1.92          | ~ (v1_funct_1 @ sk_B)
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['47', '54'])).
% 1.73/1.92  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('58', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((k1_xboole_0) != (k1_xboole_0))
% 1.73/1.92          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.73/1.92      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.73/1.92  thf('59', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.73/1.92          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 1.73/1.92      inference('simplify', [status(thm)], ['58'])).
% 1.73/1.92  thf('60', plain,
% 1.73/1.92      (![X1 : $i, X3 : $i]:
% 1.73/1.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.92  thf('61', plain,
% 1.73/1.92      (![X37 : $i, X39 : $i, X40 : $i]:
% 1.73/1.92         (((X39) != (k2_relat_1 @ X37))
% 1.73/1.92          | ((X40) = (k1_funct_1 @ X37 @ (sk_D_1 @ X40 @ X37)))
% 1.73/1.92          | ~ (r2_hidden @ X40 @ X39)
% 1.73/1.92          | ~ (v1_funct_1 @ X37)
% 1.73/1.92          | ~ (v1_relat_1 @ X37))),
% 1.73/1.92      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.73/1.92  thf('62', plain,
% 1.73/1.92      (![X37 : $i, X40 : $i]:
% 1.73/1.92         (~ (v1_relat_1 @ X37)
% 1.73/1.92          | ~ (v1_funct_1 @ X37)
% 1.73/1.92          | ~ (r2_hidden @ X40 @ (k2_relat_1 @ X37))
% 1.73/1.92          | ((X40) = (k1_funct_1 @ X37 @ (sk_D_1 @ X40 @ X37))))),
% 1.73/1.92      inference('simplify', [status(thm)], ['61'])).
% 1.73/1.92  thf('63', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.73/1.92          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 1.73/1.92              = (k1_funct_1 @ X0 @ 
% 1.73/1.92                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 1.73/1.92          | ~ (v1_funct_1 @ X0)
% 1.73/1.92          | ~ (v1_relat_1 @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['60', '62'])).
% 1.73/1.92  thf('64', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.73/1.92          | ~ (v1_relat_1 @ sk_B)
% 1.73/1.92          | ~ (v1_funct_1 @ sk_B)
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.73/1.92      inference('sup+', [status(thm)], ['59', '63'])).
% 1.73/1.92  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('67', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.73/1.92      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.73/1.92  thf('68', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.73/1.92          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 1.73/1.92      inference('simplify', [status(thm)], ['67'])).
% 1.73/1.92  thf('69', plain,
% 1.73/1.92      (![X1 : $i, X3 : $i]:
% 1.73/1.92         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.92  thf('70', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ X0)
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.73/1.92          | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['68', '69'])).
% 1.73/1.92  thf('71', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0)
% 1.73/1.92          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ X0))),
% 1.73/1.92      inference('simplify', [status(thm)], ['70'])).
% 1.73/1.92  thf('72', plain,
% 1.73/1.92      ((r1_tarski @ (k2_relat_1 @ sk_B) @ 
% 1.73/1.92        (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['37', '71'])).
% 1.73/1.92  thf('73', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.92         (~ (r2_hidden @ X0 @ X1)
% 1.73/1.92          | (r2_hidden @ X0 @ X2)
% 1.73/1.92          | ~ (r1_tarski @ X1 @ X2))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.92  thf('74', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((r2_hidden @ X0 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 1.73/1.92          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['72', '73'])).
% 1.73/1.92  thf('75', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 1.73/1.92          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 1.73/1.92          | (r2_hidden @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 1.73/1.92             (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['34', '74'])).
% 1.73/1.92  thf('76', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.73/1.92      inference('sup+', [status(thm)], ['35', '36'])).
% 1.73/1.92  thf('77', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('78', plain,
% 1.73/1.92      (![X32 : $i, X33 : $i]:
% 1.73/1.92         (~ (r2_hidden @ X33 @ (k1_relat_1 @ X32))
% 1.73/1.92          | ((k11_relat_1 @ X32 @ X33) != (k1_xboole_0))
% 1.73/1.92          | ~ (v1_relat_1 @ X32))),
% 1.73/1.92      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.73/1.92  thf('79', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.73/1.92          | ~ (v1_relat_1 @ sk_B)
% 1.73/1.92          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['77', '78'])).
% 1.73/1.92  thf('80', plain, ((v1_relat_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('81', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.73/1.92          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 1.73/1.92      inference('demod', [status(thm)], ['79', '80'])).
% 1.73/1.92  thf('82', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['76', '81'])).
% 1.73/1.92  thf(d16_relat_1, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( v1_relat_1 @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 1.73/1.92  thf('83', plain,
% 1.73/1.92      (![X28 : $i, X29 : $i]:
% 1.73/1.92         (((k11_relat_1 @ X28 @ X29) = (k9_relat_1 @ X28 @ (k1_tarski @ X29)))
% 1.73/1.92          | ~ (v1_relat_1 @ X28))),
% 1.73/1.92      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.73/1.92  thf('84', plain,
% 1.73/1.92      (![X1 : $i, X3 : $i]:
% 1.73/1.92         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.92  thf('85', plain,
% 1.73/1.92      (![X1 : $i, X3 : $i]:
% 1.73/1.92         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.92  thf('86', plain,
% 1.73/1.92      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['84', '85'])).
% 1.73/1.92  thf('87', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.73/1.92      inference('simplify', [status(thm)], ['86'])).
% 1.73/1.92  thf('88', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf(t97_relat_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( v1_relat_1 @ B ) =>
% 1.73/1.92       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.73/1.92         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.73/1.92  thf('89', plain,
% 1.73/1.92      (![X34 : $i, X35 : $i]:
% 1.73/1.92         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 1.73/1.92          | ((k7_relat_1 @ X34 @ X35) = (X34))
% 1.73/1.92          | ~ (v1_relat_1 @ X34))),
% 1.73/1.92      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.73/1.92  thf('90', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 1.73/1.92          | ~ (v1_relat_1 @ sk_B)
% 1.73/1.92          | ((k7_relat_1 @ sk_B @ X0) = (sk_B)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['88', '89'])).
% 1.73/1.92  thf('91', plain, ((v1_relat_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('92', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 1.73/1.92          | ((k7_relat_1 @ sk_B @ X0) = (sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['90', '91'])).
% 1.73/1.92  thf('93', plain, (((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['87', '92'])).
% 1.73/1.92  thf(t148_relat_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( v1_relat_1 @ B ) =>
% 1.73/1.92       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.73/1.92  thf('94', plain,
% 1.73/1.92      (![X30 : $i, X31 : $i]:
% 1.73/1.92         (((k2_relat_1 @ (k7_relat_1 @ X30 @ X31)) = (k9_relat_1 @ X30 @ X31))
% 1.73/1.92          | ~ (v1_relat_1 @ X30))),
% 1.73/1.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.73/1.92  thf('95', plain,
% 1.73/1.92      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 1.73/1.92        | ~ (v1_relat_1 @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['93', '94'])).
% 1.73/1.92  thf('96', plain, ((v1_relat_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('97', plain,
% 1.73/1.92      (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['95', '96'])).
% 1.73/1.92  thf('98', plain,
% 1.73/1.92      ((((k2_relat_1 @ sk_B) = (k11_relat_1 @ sk_B @ sk_A))
% 1.73/1.92        | ~ (v1_relat_1 @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['83', '97'])).
% 1.73/1.92  thf('99', plain, ((v1_relat_1 @ sk_B)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('100', plain, (((k2_relat_1 @ sk_B) = (k11_relat_1 @ sk_B @ sk_A))),
% 1.73/1.92      inference('demod', [status(thm)], ['98', '99'])).
% 1.73/1.92  thf('101', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 1.73/1.92      inference('demod', [status(thm)], ['82', '100'])).
% 1.73/1.92  thf('102', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 1.73/1.92          | (r2_hidden @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 1.73/1.92             (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 1.73/1.92      inference('simplify_reflect-', [status(thm)], ['75', '101'])).
% 1.73/1.92  thf('103', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.73/1.92          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.73/1.92      inference('sup-', [status(thm)], ['12', '16'])).
% 1.73/1.92  thf('104', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 1.73/1.92          | ~ (zip_tseitin_0 @ (sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 1.73/1.92               (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 1.73/1.92               (k1_funct_1 @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['102', '103'])).
% 1.73/1.92  thf('105', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((sk_C_1 @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 1.73/1.92          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['33', '104'])).
% 1.73/1.92  thf('106', plain,
% 1.73/1.92      (![X26 : $i, X27 : $i]:
% 1.73/1.92         (((X26) = (k1_xboole_0))
% 1.73/1.92          | ((sk_C_1 @ X27 @ X26) != (X27))
% 1.73/1.92          | ((X26) = (k1_tarski @ X27)))),
% 1.73/1.92      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.73/1.92  thf('107', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 1.73/1.92          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 1.73/1.92          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 1.73/1.92          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['105', '106'])).
% 1.73/1.92  thf('108', plain,
% 1.73/1.92      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 1.73/1.92        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 1.73/1.92      inference('simplify', [status(thm)], ['107'])).
% 1.73/1.92  thf('109', plain,
% 1.73/1.92      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.92  thf('110', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 1.73/1.92      inference('demod', [status(thm)], ['82', '100'])).
% 1.73/1.92  thf('111', plain, ($false),
% 1.73/1.92      inference('simplify_reflect-', [status(thm)], ['108', '109', '110'])).
% 1.73/1.92  
% 1.73/1.92  % SZS output end Refutation
% 1.73/1.92  
% 1.73/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
