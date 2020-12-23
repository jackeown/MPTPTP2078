%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TC6ezWNw0B

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:25 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 217 expanded)
%              Number of leaves         :   16 (  69 expanded)
%              Depth                    :   21
%              Number of atoms          :  798 (2680 expanded)
%              Number of equality atoms :   84 ( 324 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
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

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
        = sk_A )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B )
        = sk_A )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
        = X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( ( sk_C_1 @ X8 @ X9 )
       != ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ X0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B )
        = sk_A )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = sk_A )
    | ( ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = sk_A )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('36',plain,
    ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( ( sk_C_1 @ X8 @ X9 )
        = ( k1_funct_1 @ X9 @ ( sk_D @ X8 @ X9 ) ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('38',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( ( sk_C_1 @ X8 @ X9 )
       != ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('sup-',[status(thm)],['3','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TC6ezWNw0B
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:05:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.63  % Solved by: fo/fo7.sh
% 0.43/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.63  % done 247 iterations in 0.168s
% 0.43/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.63  % SZS output start Refutation
% 0.43/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.43/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.43/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.63  thf(t14_funct_1, conjecture,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.63       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.43/0.63         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.63    (~( ![A:$i,B:$i]:
% 0.43/0.63        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.63          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.43/0.63            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.43/0.63    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.43/0.63  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(d1_tarski, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.43/0.63  thf('1', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.63  thf('2', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['1'])).
% 0.43/0.63  thf('3', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.43/0.63      inference('sup+', [status(thm)], ['0', '2'])).
% 0.43/0.63  thf(t69_enumset1, axiom,
% 0.43/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.63  thf('4', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf(d5_funct_1, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.63       ( ![B:$i]:
% 0.43/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.43/0.63           ( ![C:$i]:
% 0.43/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.63               ( ?[D:$i]:
% 0.43/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.43/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.43/0.63  thf('5', plain,
% 0.43/0.63      (![X8 : $i, X9 : $i]:
% 0.43/0.63         ((r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.43/0.63          | (r2_hidden @ (sk_D @ X8 @ X9) @ (k1_relat_1 @ X9))
% 0.43/0.63          | ((X8) = (k2_relat_1 @ X9))
% 0.43/0.63          | ~ (v1_funct_1 @ X9)
% 0.43/0.63          | ~ (v1_relat_1 @ X9))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.43/0.63  thf('6', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('7', plain,
% 0.43/0.63      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.63  thf('8', plain,
% 0.43/0.63      (![X0 : $i, X3 : $i]:
% 0.43/0.63         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['7'])).
% 0.43/0.63  thf('9', plain,
% 0.43/0.63      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['6', '8'])).
% 0.43/0.63  thf('10', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ sk_B)
% 0.43/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63          | ((X0) = (k2_relat_1 @ sk_B))
% 0.43/0.63          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0)
% 0.43/0.63          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['5', '9'])).
% 0.43/0.63  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('13', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((X0) = (k2_relat_1 @ sk_B))
% 0.43/0.63          | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0)
% 0.43/0.63          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.43/0.63      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.43/0.63  thf('14', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf('15', plain,
% 0.43/0.63      (![X0 : $i, X3 : $i]:
% 0.43/0.63         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['7'])).
% 0.43/0.63  thf('16', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.63  thf('17', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((sk_D @ (k2_tarski @ X0 @ X0) @ sk_B) = (sk_A))
% 0.43/0.63          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B))
% 0.43/0.63          | ((sk_C_1 @ (k2_tarski @ X0 @ X0) @ sk_B) = (X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['13', '16'])).
% 0.43/0.63  thf('18', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((sk_D @ (k1_tarski @ X0) @ sk_B) = (sk_A))
% 0.43/0.63          | ((sk_C_1 @ (k2_tarski @ X0 @ X0) @ sk_B) = (X0))
% 0.43/0.63          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['4', '17'])).
% 0.43/0.63  thf('19', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.43/0.63      inference('sup+', [status(thm)], ['0', '2'])).
% 0.43/0.63  thf('20', plain,
% 0.43/0.63      (![X8 : $i, X9 : $i]:
% 0.43/0.63         ((r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.43/0.63          | (r2_hidden @ (sk_D @ X8 @ X9) @ (k1_relat_1 @ X9))
% 0.43/0.63          | ((X8) = (k2_relat_1 @ X9))
% 0.43/0.63          | ~ (v1_funct_1 @ X9)
% 0.43/0.63          | ~ (v1_relat_1 @ X9))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.43/0.63  thf('21', plain,
% 0.43/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.43/0.63         (~ (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.43/0.63          | ((sk_C_1 @ X8 @ X9) != (k1_funct_1 @ X9 @ X10))
% 0.43/0.63          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.43/0.63          | ((X8) = (k2_relat_1 @ X9))
% 0.43/0.63          | ~ (v1_funct_1 @ X9)
% 0.43/0.63          | ~ (v1_relat_1 @ X9))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.43/0.63  thf('22', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ X1)
% 0.43/0.63          | ~ (v1_funct_1 @ X1)
% 0.43/0.63          | ((X0) = (k2_relat_1 @ X1))
% 0.43/0.63          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.43/0.63          | ~ (v1_relat_1 @ X1)
% 0.43/0.63          | ~ (v1_funct_1 @ X1)
% 0.43/0.63          | ((X0) = (k2_relat_1 @ X1))
% 0.43/0.63          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.43/0.63          | ((sk_C_1 @ X0 @ X1) != (k1_funct_1 @ X1 @ X2)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.63  thf('23', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         (((sk_C_1 @ X0 @ X1) != (k1_funct_1 @ X1 @ X2))
% 0.43/0.63          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.43/0.63          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.43/0.63          | ((X0) = (k2_relat_1 @ X1))
% 0.43/0.63          | ~ (v1_funct_1 @ X1)
% 0.43/0.63          | ~ (v1_relat_1 @ X1))),
% 0.43/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.43/0.63  thf('24', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ sk_B)
% 0.43/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63          | ((X0) = (k2_relat_1 @ sk_B))
% 0.43/0.63          | (r2_hidden @ (sk_D @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.43/0.63          | ((sk_C_1 @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['19', '23'])).
% 0.43/0.63  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('27', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((X0) = (k2_relat_1 @ sk_B))
% 0.43/0.63          | (r2_hidden @ (sk_D @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.43/0.63          | ((sk_C_1 @ X0 @ sk_B) != (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.43/0.63  thf('28', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((X0) != (k1_funct_1 @ sk_B @ sk_A))
% 0.43/0.63          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B))
% 0.43/0.63          | ((sk_D @ (k1_tarski @ X0) @ sk_B) = (sk_A))
% 0.43/0.63          | (r2_hidden @ (sk_D @ (k2_tarski @ X0 @ X0) @ sk_B) @ 
% 0.43/0.63             (k1_relat_1 @ sk_B))
% 0.43/0.63          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ sk_B)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['18', '27'])).
% 0.43/0.63  thf('29', plain,
% 0.43/0.63      (((r2_hidden @ 
% 0.43/0.63         (sk_D @ 
% 0.43/0.63          (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)) @ 
% 0.43/0.63          sk_B) @ 
% 0.43/0.63         (k1_relat_1 @ sk_B))
% 0.43/0.63        | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) = (sk_A))
% 0.43/0.63        | ((k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.43/0.63            = (k2_relat_1 @ sk_B)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.43/0.63  thf('30', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf('31', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf('32', plain,
% 0.43/0.63      (((r2_hidden @ 
% 0.43/0.63         (sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.43/0.63         (k1_relat_1 @ sk_B))
% 0.43/0.63        | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) = (sk_A))
% 0.43/0.63        | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.43/0.63  thf('33', plain,
% 0.43/0.63      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('34', plain,
% 0.43/0.63      (((r2_hidden @ 
% 0.43/0.63         (sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) @ 
% 0.43/0.63         (k1_relat_1 @ sk_B))
% 0.43/0.63        | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) = (sk_A)))),
% 0.43/0.63      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.43/0.63  thf('35', plain,
% 0.43/0.63      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['6', '8'])).
% 0.43/0.63  thf('36', plain,
% 0.43/0.63      (((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B) = (sk_A))),
% 0.43/0.63      inference('clc', [status(thm)], ['34', '35'])).
% 0.43/0.63  thf('37', plain,
% 0.43/0.63      (![X8 : $i, X9 : $i]:
% 0.43/0.63         ((r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.43/0.63          | ((sk_C_1 @ X8 @ X9) = (k1_funct_1 @ X9 @ (sk_D @ X8 @ X9)))
% 0.43/0.63          | ((X8) = (k2_relat_1 @ X9))
% 0.43/0.63          | ~ (v1_funct_1 @ X9)
% 0.43/0.63          | ~ (v1_relat_1 @ X9))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.43/0.63  thf('38', plain,
% 0.43/0.63      (![X0 : $i, X3 : $i]:
% 0.43/0.63         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['7'])).
% 0.43/0.63  thf('39', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (v1_relat_1 @ X1)
% 0.43/0.63          | ~ (v1_funct_1 @ X1)
% 0.43/0.63          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.43/0.63          | ((sk_C_1 @ (k1_tarski @ X0) @ X1)
% 0.43/0.63              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 0.43/0.63          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.63  thf('40', plain,
% 0.43/0.63      ((((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.43/0.63          = (k1_funct_1 @ sk_B @ sk_A))
% 0.43/0.63        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.43/0.63            = (k1_funct_1 @ sk_B @ sk_A))
% 0.43/0.63        | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.43/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.43/0.63      inference('sup+', [status(thm)], ['36', '39'])).
% 0.43/0.63  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('43', plain,
% 0.43/0.63      ((((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.43/0.63          = (k1_funct_1 @ sk_B @ sk_A))
% 0.43/0.63        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.43/0.63            = (k1_funct_1 @ sk_B @ sk_A))
% 0.43/0.63        | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.43/0.63  thf('44', plain,
% 0.43/0.63      ((((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.43/0.63        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.43/0.63            = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['43'])).
% 0.43/0.63  thf('45', plain,
% 0.43/0.63      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('46', plain,
% 0.43/0.63      (((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.43/0.63         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.43/0.63      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.43/0.63  thf('47', plain,
% 0.43/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.43/0.63         (~ (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.43/0.63          | ((sk_C_1 @ X8 @ X9) != (k1_funct_1 @ X9 @ X10))
% 0.43/0.63          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.43/0.63          | ((X8) = (k2_relat_1 @ X9))
% 0.43/0.63          | ~ (v1_funct_1 @ X9)
% 0.43/0.63          | ~ (v1_relat_1 @ X9))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.43/0.63  thf('48', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.43/0.63             (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.43/0.63          | ~ (v1_relat_1 @ sk_B)
% 0.43/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.43/0.63          | ((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.43/0.63          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.43/0.63          | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.43/0.63              != (k1_funct_1 @ sk_B @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.63  thf('49', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['1'])).
% 0.43/0.63  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('52', plain,
% 0.43/0.63      (((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.43/0.63         = (k1_funct_1 @ sk_B @ sk_A))),
% 0.43/0.63      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.43/0.63  thf('53', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.43/0.63          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.43/0.63          | ((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ X0)))),
% 0.43/0.63      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.43/0.63  thf('54', plain,
% 0.43/0.63      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('55', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.43/0.63          | ((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ X0)))),
% 0.43/0.63      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.43/0.63  thf('56', plain,
% 0.43/0.63      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['6', '8'])).
% 0.43/0.63  thf('57', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))),
% 0.43/0.63      inference('clc', [status(thm)], ['55', '56'])).
% 0.43/0.63  thf('58', plain, ($false), inference('sup-', [status(thm)], ['3', '57'])).
% 0.43/0.63  
% 0.43/0.63  % SZS output end Refutation
% 0.43/0.63  
% 0.50/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
