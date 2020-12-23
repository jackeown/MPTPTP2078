%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0674+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9tRE33Jk4J

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:18 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 184 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   23
%              Number of atoms          : 1037 (2723 expanded)
%              Number of equality atoms :   71 ( 200 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ X13 @ ( k1_tarski @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X16 != X15 )
      | ( r2_hidden @ X16 @ X17 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X15: $i] :
      ( r2_hidden @ X15 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t117_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k11_relat_1 @ B @ A )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_funct_1])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k1_funct_1 @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    zip_tseitin_0 @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    zip_tseitin_0 @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['2','6'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( X18 = X15 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ ( k1_tarski @ X0 ) @ X2 @ X1 ) @ X2 )
      | ( ( k1_tarski @ X0 )
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X2 )
        = ( k9_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_E @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('18',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( sk_E @ X2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_E @ X0 @ ( k1_tarski @ X2 ) @ X1 )
        = X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k1_tarski @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k1_tarski @ X2 ) ) )
      | ~ ( zip_tseitin_0 @ X3 @ ( sk_D @ X0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( zip_tseitin_0 @ X3 @ ( sk_D @ X0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k1_tarski @ X2 ) @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k1_tarski @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( sk_E @ X0 @ ( k1_tarski @ X2 ) @ X1 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( zip_tseitin_0 @ X3 @ X0 @ ( k1_tarski @ X2 ) @ X1 )
      | ( ( sk_E @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X2 ) @ X1 )
        = X2 )
      | ( ( k1_tarski @ X0 )
        = ( k9_relat_1 @ X1 @ ( k1_tarski @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( sk_E @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X2 ) @ X1 )
        = X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k9_relat_1 @ X1 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k9_relat_1 @ X1 @ ( k1_tarski @ X2 ) ) )
      | ( ( sk_E @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X2 ) @ X1 )
        = X2 )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( sk_E @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_A )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( sk_E @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_A )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( zip_tseitin_0 @ sk_A @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('38',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( r2_hidden @ X15 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) @ sk_B )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) @ sk_B )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).


%------------------------------------------------------------------------------
