%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0619+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Xokn1Ziw4

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 128 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  508 (1542 expanded)
%              Number of equality atoms :   61 ( 202 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','2'])).

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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ( X5
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( ( sk_C_1 @ X5 @ X6 )
        = ( k1_funct_1 @ X6 @ ( sk_D @ X5 @ X6 ) ) )
      | ( X5
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('16',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( ( sk_C_1 @ X5 @ X6 )
       != ( k1_funct_1 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X6 ) )
      | ( X5
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','37'])).


%------------------------------------------------------------------------------
