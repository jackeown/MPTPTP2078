%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZLOrgCeYdU

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:43 EST 2020

% Result     : Theorem 3.73s
% Output     : Refutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 385 expanded)
%              Number of leaves         :   25 ( 120 expanded)
%              Depth                    :   20
%              Number of atoms          : 1012 (4286 expanded)
%              Number of equality atoms :  103 ( 503 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('3',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X14 ) @ ( k4_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C_3 )
      = ( k1_tarski @ ( k4_tarski @ X0 @ ( k4_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X19 )
      | ( r2_hidden @ X17 @ X20 )
      | ( X20
       != ( k1_relat_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X19 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_D_1 @ X21 @ X19 ) ) @ X19 )
      | ( X20
       != ( k1_relat_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('16',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_D_1 @ X21 @ X19 ) ) @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ X1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D_1 @ X1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('25',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22
        = ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X22 @ X19 ) @ ( sk_D @ X22 @ X19 ) ) @ X19 )
      | ( r2_hidden @ ( sk_C_1 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('32',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( X22
        = ( k1_relat_1 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X22 @ X19 ) @ X23 ) @ X19 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ ( k1_tarski @ ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ sk_C_3 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['23','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ sk_C_3 ) )
      = ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','22'])).

thf('42',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference('sup+',[status(thm)],['42','43'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('45',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29
        = ( k2_relat_1 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X29 @ X26 ) @ ( sk_C_2 @ X29 @ X26 ) ) @ X26 )
      | ( r2_hidden @ ( sk_C_2 @ X29 @ X26 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('46',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_3 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ X0 @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ sk_C_3 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ sk_C_3 ) )
    | ( ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['52'])).

thf('55',plain,(
    ! [X26: $i,X29: $i,X30: $i] :
      ( ( X29
        = ( k2_relat_1 @ X26 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ ( sk_C_2 @ X29 @ X26 ) ) @ X26 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X29 @ X26 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_B ) @ sk_C_3 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ sk_C_3 )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_C_3 ) )
      = ( k1_tarski @ ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ sk_C_3 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','64'])).

thf('66',plain,
    ( sk_C_3
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('68',plain,
    ( sk_C_3
    = ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( sk_C_3
      = ( k1_tarski @ ( sk_D_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ sk_C_3 ) ) ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['40','69'])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('74',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['71'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
     != ( k2_relat_1 @ sk_C_3 ) )
   <= ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_3 )
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['71'])).

thf('78',plain,(
    ( k1_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    ( k1_relat_1 @ sk_C_3 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['72','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZLOrgCeYdU
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.73/3.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.73/3.97  % Solved by: fo/fo7.sh
% 3.73/3.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.73/3.97  % done 2620 iterations in 3.467s
% 3.73/3.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.73/3.97  % SZS output start Refutation
% 3.73/3.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.73/3.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.73/3.97  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 3.73/3.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.73/3.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.73/3.97  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.73/3.97  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.73/3.97  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 3.73/3.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.73/3.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.73/3.97  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.73/3.97  thf(sk_A_type, type, sk_A: $i).
% 3.73/3.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.73/3.97  thf(sk_B_type, type, sk_B: $i).
% 3.73/3.97  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.73/3.97  thf(sk_C_3_type, type, sk_C_3: $i).
% 3.73/3.97  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.73/3.97  thf(t70_enumset1, axiom,
% 3.73/3.97    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.73/3.97  thf('0', plain,
% 3.73/3.97      (![X6 : $i, X7 : $i]:
% 3.73/3.97         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 3.73/3.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.73/3.97  thf(t69_enumset1, axiom,
% 3.73/3.97    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.73/3.97  thf('1', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 3.73/3.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.73/3.97  thf('2', plain,
% 3.73/3.97      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 3.73/3.97      inference('sup+', [status(thm)], ['0', '1'])).
% 3.73/3.97  thf(t23_relat_1, conjecture,
% 3.73/3.97    (![A:$i,B:$i,C:$i]:
% 3.73/3.97     ( ( v1_relat_1 @ C ) =>
% 3.73/3.97       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 3.73/3.97         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 3.73/3.97           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 3.73/3.97  thf(zf_stmt_0, negated_conjecture,
% 3.73/3.97    (~( ![A:$i,B:$i,C:$i]:
% 3.73/3.97        ( ( v1_relat_1 @ C ) =>
% 3.73/3.97          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 3.73/3.97            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 3.73/3.97              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 3.73/3.97    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 3.73/3.97  thf('3', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.73/3.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.97  thf('4', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 3.73/3.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.73/3.97  thf(t36_zfmisc_1, axiom,
% 3.73/3.97    (![A:$i,B:$i,C:$i]:
% 3.73/3.97     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 3.73/3.97         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 3.73/3.97       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 3.73/3.97         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 3.73/3.97  thf('5', plain,
% 3.73/3.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X13) @ (k2_tarski @ X14 @ X15))
% 3.73/3.97           = (k2_tarski @ (k4_tarski @ X13 @ X14) @ (k4_tarski @ X13 @ X15)))),
% 3.73/3.97      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.73/3.97  thf('6', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 3.73/3.97           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.73/3.97      inference('sup+', [status(thm)], ['4', '5'])).
% 3.73/3.97  thf('7', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 3.73/3.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.73/3.97  thf('8', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.73/3.97           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.73/3.97      inference('demod', [status(thm)], ['6', '7'])).
% 3.73/3.97  thf('9', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C_3)
% 3.73/3.97           = (k1_tarski @ (k4_tarski @ X0 @ (k4_tarski @ sk_A @ sk_B))))),
% 3.73/3.97      inference('sup+', [status(thm)], ['3', '8'])).
% 3.73/3.97  thf(d1_tarski, axiom,
% 3.73/3.97    (![A:$i,B:$i]:
% 3.73/3.97     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.73/3.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.73/3.97  thf('10', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.73/3.97         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 3.73/3.97      inference('cnf', [status(esa)], [d1_tarski])).
% 3.73/3.97  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.73/3.97      inference('simplify', [status(thm)], ['10'])).
% 3.73/3.97  thf(d4_relat_1, axiom,
% 3.73/3.97    (![A:$i,B:$i]:
% 3.73/3.97     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.73/3.97       ( ![C:$i]:
% 3.73/3.97         ( ( r2_hidden @ C @ B ) <=>
% 3.73/3.97           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.73/3.97  thf('12', plain,
% 3.73/3.97      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ X19)
% 3.73/3.97          | (r2_hidden @ X17 @ X20)
% 3.73/3.97          | ((X20) != (k1_relat_1 @ X19)))),
% 3.73/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.73/3.97  thf('13', plain,
% 3.73/3.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.73/3.97         ((r2_hidden @ X17 @ (k1_relat_1 @ X19))
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ X19))),
% 3.73/3.97      inference('simplify', [status(thm)], ['12'])).
% 3.73/3.97  thf('14', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         (r2_hidden @ X1 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 3.73/3.97      inference('sup-', [status(thm)], ['11', '13'])).
% 3.73/3.97  thf('15', plain,
% 3.73/3.97      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.73/3.97         (~ (r2_hidden @ X21 @ X20)
% 3.73/3.97          | (r2_hidden @ (k4_tarski @ X21 @ (sk_D_1 @ X21 @ X19)) @ X19)
% 3.73/3.97          | ((X20) != (k1_relat_1 @ X19)))),
% 3.73/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.73/3.97  thf('16', plain,
% 3.73/3.97      (![X19 : $i, X21 : $i]:
% 3.73/3.97         ((r2_hidden @ (k4_tarski @ X21 @ (sk_D_1 @ X21 @ X19)) @ X19)
% 3.73/3.97          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X19)))),
% 3.73/3.97      inference('simplify', [status(thm)], ['15'])).
% 3.73/3.97  thf('17', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         (r2_hidden @ 
% 3.73/3.97          (k4_tarski @ X1 @ (sk_D_1 @ X1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))) @ 
% 3.73/3.97          (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['14', '16'])).
% 3.73/3.97  thf('18', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.73/3.97           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.73/3.97      inference('demod', [status(thm)], ['6', '7'])).
% 3.73/3.97  thf(t129_zfmisc_1, axiom,
% 3.73/3.97    (![A:$i,B:$i,C:$i,D:$i]:
% 3.73/3.97     ( ( r2_hidden @
% 3.73/3.97         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 3.73/3.97       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 3.73/3.97  thf('19', plain,
% 3.73/3.97      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.73/3.97         (((X10) = (X11))
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ 
% 3.73/3.97               (k2_zfmisc_1 @ X9 @ (k1_tarski @ X11))))),
% 3.73/3.97      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 3.73/3.97  thf('20', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.73/3.97             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.73/3.97          | ((X2) = (X0)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['18', '19'])).
% 3.73/3.97  thf('21', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((sk_D_1 @ X1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (X0))),
% 3.73/3.97      inference('sup-', [status(thm)], ['17', '20'])).
% 3.73/3.97  thf('22', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C_3))
% 3.73/3.97           = (k4_tarski @ sk_A @ sk_B))),
% 3.73/3.97      inference('sup+', [status(thm)], ['9', '21'])).
% 3.73/3.97  thf('23', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k1_enumset1 @ X0 @ X0 @ X0) @ sk_C_3))
% 3.73/3.97           = (k4_tarski @ sk_A @ sk_B))),
% 3.73/3.97      inference('sup+', [status(thm)], ['2', '22'])).
% 3.73/3.97  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.73/3.97      inference('simplify', [status(thm)], ['10'])).
% 3.73/3.97  thf('25', plain,
% 3.73/3.97      (![X19 : $i, X22 : $i]:
% 3.73/3.97         (((X22) = (k1_relat_1 @ X19))
% 3.73/3.97          | (r2_hidden @ 
% 3.73/3.97             (k4_tarski @ (sk_C_1 @ X22 @ X19) @ (sk_D @ X22 @ X19)) @ X19)
% 3.73/3.97          | (r2_hidden @ (sk_C_1 @ X22 @ X19) @ X22))),
% 3.73/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.73/3.97  thf('26', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.73/3.97           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.73/3.97      inference('demod', [status(thm)], ['6', '7'])).
% 3.73/3.97  thf('27', plain,
% 3.73/3.97      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.73/3.97         ((r2_hidden @ X8 @ X9)
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ 
% 3.73/3.97               (k2_zfmisc_1 @ X9 @ (k1_tarski @ X11))))),
% 3.73/3.97      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 3.73/3.97  thf('28', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.73/3.97             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.73/3.97          | (r2_hidden @ X3 @ (k1_tarski @ X1)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['26', '27'])).
% 3.73/3.97  thf('29', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.73/3.97         ((r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 3.73/3.97          | ((X2) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))
% 3.73/3.97          | (r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ 
% 3.73/3.97             (k1_tarski @ X1)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['25', '28'])).
% 3.73/3.97  thf('30', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((r2_hidden @ 
% 3.73/3.97           (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 3.73/3.97           (k1_tarski @ X0))
% 3.73/3.97          | ((k1_tarski @ X0)
% 3.73/3.97              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 3.73/3.97      inference('eq_fact', [status(thm)], ['29'])).
% 3.73/3.97  thf('31', plain,
% 3.73/3.97      (![X0 : $i, X2 : $i, X3 : $i]:
% 3.73/3.97         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 3.73/3.97      inference('cnf', [status(esa)], [d1_tarski])).
% 3.73/3.97  thf('32', plain,
% 3.73/3.97      (![X0 : $i, X3 : $i]:
% 3.73/3.97         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 3.73/3.97      inference('simplify', [status(thm)], ['31'])).
% 3.73/3.97  thf('33', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         (((k1_tarski @ X0)
% 3.73/3.97            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 3.73/3.97          | ((sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 3.73/3.97              = (X0)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['30', '32'])).
% 3.73/3.97  thf('34', plain,
% 3.73/3.97      (![X19 : $i, X22 : $i, X23 : $i]:
% 3.73/3.97         (((X22) = (k1_relat_1 @ X19))
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X22 @ X19) @ X23) @ X19)
% 3.73/3.97          | ~ (r2_hidden @ (sk_C_1 @ X22 @ X19) @ X22))),
% 3.73/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.73/3.97  thf('35', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 3.73/3.97             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 3.73/3.97          | ((k1_tarski @ X0)
% 3.73/3.97              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 3.73/3.97          | ~ (r2_hidden @ 
% 3.73/3.97               (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 3.73/3.97               (k1_tarski @ X0))
% 3.73/3.97          | ((k1_tarski @ X0)
% 3.73/3.97              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 3.73/3.97      inference('sup-', [status(thm)], ['33', '34'])).
% 3.73/3.97  thf('36', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.73/3.97         (~ (r2_hidden @ 
% 3.73/3.97             (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 3.73/3.97             (k1_tarski @ X0))
% 3.73/3.97          | ((k1_tarski @ X0)
% 3.73/3.97              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 3.73/3.97               (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 3.73/3.97      inference('simplify', [status(thm)], ['35'])).
% 3.73/3.97  thf('37', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((r2_hidden @ 
% 3.73/3.97           (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 3.73/3.97           (k1_tarski @ X0))
% 3.73/3.97          | ((k1_tarski @ X0)
% 3.73/3.97              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 3.73/3.97      inference('eq_fact', [status(thm)], ['29'])).
% 3.73/3.97  thf('38', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 3.73/3.97             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 3.73/3.97          | ((k1_tarski @ X0)
% 3.73/3.97              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 3.73/3.97      inference('clc', [status(thm)], ['36', '37'])).
% 3.73/3.97  thf('39', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 3.73/3.97      inference('sup-', [status(thm)], ['24', '38'])).
% 3.73/3.97  thf('40', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((k1_tarski @ sk_A)
% 3.73/3.97           = (k1_relat_1 @ 
% 3.73/3.97              (k1_tarski @ 
% 3.73/3.97               (sk_D_1 @ X0 @ 
% 3.73/3.97                (k2_zfmisc_1 @ (k1_enumset1 @ X0 @ X0 @ X0) @ sk_C_3)))))),
% 3.73/3.97      inference('sup+', [status(thm)], ['23', '39'])).
% 3.73/3.97  thf('41', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((sk_D_1 @ X0 @ (k2_zfmisc_1 @ (k1_enumset1 @ X0 @ X0 @ X0) @ sk_C_3))
% 3.73/3.97           = (k4_tarski @ sk_A @ sk_B))),
% 3.73/3.97      inference('sup+', [status(thm)], ['2', '22'])).
% 3.73/3.97  thf('42', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.73/3.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.97  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.73/3.97      inference('simplify', [status(thm)], ['10'])).
% 3.73/3.97  thf('44', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 3.73/3.97      inference('sup+', [status(thm)], ['42', '43'])).
% 3.73/3.97  thf(d5_relat_1, axiom,
% 3.73/3.97    (![A:$i,B:$i]:
% 3.73/3.97     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.73/3.97       ( ![C:$i]:
% 3.73/3.97         ( ( r2_hidden @ C @ B ) <=>
% 3.73/3.97           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.73/3.97  thf('45', plain,
% 3.73/3.97      (![X26 : $i, X29 : $i]:
% 3.73/3.97         (((X29) = (k2_relat_1 @ X26))
% 3.73/3.97          | (r2_hidden @ 
% 3.73/3.97             (k4_tarski @ (sk_D_2 @ X29 @ X26) @ (sk_C_2 @ X29 @ X26)) @ X26)
% 3.73/3.97          | (r2_hidden @ (sk_C_2 @ X29 @ X26) @ X29))),
% 3.73/3.97      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.73/3.97  thf('46', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.73/3.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.97  thf('47', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ 
% 3.73/3.97             (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 3.73/3.97          | ((X2) = (X0)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['18', '19'])).
% 3.73/3.97  thf('48', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_3) | ((X0) = (sk_B)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['46', '47'])).
% 3.73/3.97  thf('49', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ X0)
% 3.73/3.97          | ((X0) = (k2_relat_1 @ sk_C_3))
% 3.73/3.97          | ((sk_C_2 @ X0 @ sk_C_3) = (sk_B)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['45', '48'])).
% 3.73/3.97  thf('50', plain,
% 3.73/3.97      (![X0 : $i, X3 : $i]:
% 3.73/3.97         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 3.73/3.97      inference('simplify', [status(thm)], ['31'])).
% 3.73/3.97  thf('51', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         (((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (sk_B))
% 3.73/3.97          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3))
% 3.73/3.97          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['49', '50'])).
% 3.73/3.97  thf('52', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         (((sk_B) != (X0))
% 3.73/3.97          | ((sk_C_2 @ (k1_tarski @ X0) @ sk_C_3) = (X0))
% 3.73/3.97          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_3)))),
% 3.73/3.97      inference('eq_fact', [status(thm)], ['51'])).
% 3.73/3.97  thf('53', plain,
% 3.73/3.97      ((((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.73/3.97        | ((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B)))),
% 3.73/3.97      inference('simplify', [status(thm)], ['52'])).
% 3.73/3.97  thf('54', plain,
% 3.73/3.97      ((((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.73/3.97        | ((sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) = (sk_B)))),
% 3.73/3.97      inference('simplify', [status(thm)], ['52'])).
% 3.73/3.97  thf('55', plain,
% 3.73/3.97      (![X26 : $i, X29 : $i, X30 : $i]:
% 3.73/3.97         (((X29) = (k2_relat_1 @ X26))
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ X30 @ (sk_C_2 @ X29 @ X26)) @ X26)
% 3.73/3.97          | ~ (r2_hidden @ (sk_C_2 @ X29 @ X26) @ X29))),
% 3.73/3.97      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.73/3.97  thf('56', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 3.73/3.97          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.73/3.97          | ~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 3.73/3.97               (k1_tarski @ sk_B))
% 3.73/3.97          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['54', '55'])).
% 3.73/3.97  thf('57', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_B) @ sk_C_3) @ 
% 3.73/3.97             (k1_tarski @ sk_B))
% 3.73/3.97          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3))),
% 3.73/3.97      inference('simplify', [status(thm)], ['56'])).
% 3.73/3.97  thf('58', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 3.73/3.97          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 3.73/3.97          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 3.73/3.97      inference('sup-', [status(thm)], ['53', '57'])).
% 3.73/3.97  thf('59', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.73/3.97      inference('simplify', [status(thm)], ['10'])).
% 3.73/3.97  thf('60', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))
% 3.73/3.97          | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 3.73/3.97          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 3.73/3.97      inference('demod', [status(thm)], ['58', '59'])).
% 3.73/3.97  thf('61', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         (~ (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ sk_C_3)
% 3.73/3.97          | ((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3)))),
% 3.73/3.97      inference('simplify', [status(thm)], ['60'])).
% 3.73/3.97  thf('62', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))),
% 3.73/3.97      inference('sup-', [status(thm)], ['44', '61'])).
% 3.73/3.97  thf('63', plain,
% 3.73/3.97      (![X0 : $i, X1 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.73/3.97           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 3.73/3.97      inference('demod', [status(thm)], ['6', '7'])).
% 3.73/3.97  thf('64', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ (k2_relat_1 @ sk_C_3))
% 3.73/3.97           = (k1_tarski @ (k4_tarski @ X0 @ sk_B)))),
% 3.73/3.97      inference('sup+', [status(thm)], ['62', '63'])).
% 3.73/3.97  thf('65', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_C_3))
% 3.73/3.97           = (k1_tarski @ 
% 3.73/3.97              (sk_D_1 @ X0 @ 
% 3.73/3.97               (k2_zfmisc_1 @ (k1_enumset1 @ X0 @ X0 @ X0) @ sk_C_3))))),
% 3.73/3.97      inference('sup+', [status(thm)], ['41', '64'])).
% 3.73/3.97  thf('66', plain, (((sk_C_3) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))),
% 3.73/3.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.97  thf('67', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ (k2_relat_1 @ sk_C_3))
% 3.73/3.97           = (k1_tarski @ (k4_tarski @ X0 @ sk_B)))),
% 3.73/3.97      inference('sup+', [status(thm)], ['62', '63'])).
% 3.73/3.97  thf('68', plain,
% 3.73/3.97      (((sk_C_3) = (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_C_3)))),
% 3.73/3.97      inference('demod', [status(thm)], ['66', '67'])).
% 3.73/3.97  thf('69', plain,
% 3.73/3.97      (![X0 : $i]:
% 3.73/3.97         ((sk_C_3)
% 3.73/3.97           = (k1_tarski @ 
% 3.73/3.97              (sk_D_1 @ X0 @ 
% 3.73/3.97               (k2_zfmisc_1 @ (k1_enumset1 @ X0 @ X0 @ X0) @ sk_C_3))))),
% 3.73/3.97      inference('demod', [status(thm)], ['65', '68'])).
% 3.73/3.97  thf('70', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_3))),
% 3.73/3.97      inference('demod', [status(thm)], ['40', '69'])).
% 3.73/3.97  thf('71', plain,
% 3.73/3.97      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))
% 3.73/3.97        | ((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))),
% 3.73/3.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.97  thf('72', plain,
% 3.73/3.97      ((((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A)))
% 3.73/3.97         <= (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))))),
% 3.73/3.97      inference('split', [status(esa)], ['71'])).
% 3.73/3.97  thf('73', plain, (((k1_tarski @ sk_B) = (k2_relat_1 @ sk_C_3))),
% 3.73/3.97      inference('sup-', [status(thm)], ['44', '61'])).
% 3.73/3.97  thf('74', plain,
% 3.73/3.97      ((((k2_relat_1 @ sk_C_3) != (k1_tarski @ sk_B)))
% 3.73/3.97         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 3.73/3.97      inference('split', [status(esa)], ['71'])).
% 3.73/3.97  thf('75', plain,
% 3.73/3.97      ((((k2_relat_1 @ sk_C_3) != (k2_relat_1 @ sk_C_3)))
% 3.73/3.97         <= (~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B))))),
% 3.73/3.97      inference('sup-', [status(thm)], ['73', '74'])).
% 3.73/3.97  thf('76', plain, ((((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 3.73/3.97      inference('simplify', [status(thm)], ['75'])).
% 3.73/3.97  thf('77', plain,
% 3.73/3.97      (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A))) | 
% 3.73/3.97       ~ (((k2_relat_1 @ sk_C_3) = (k1_tarski @ sk_B)))),
% 3.73/3.97      inference('split', [status(esa)], ['71'])).
% 3.73/3.97  thf('78', plain, (~ (((k1_relat_1 @ sk_C_3) = (k1_tarski @ sk_A)))),
% 3.73/3.97      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 3.73/3.97  thf('79', plain, (((k1_relat_1 @ sk_C_3) != (k1_tarski @ sk_A))),
% 3.73/3.97      inference('simpl_trail', [status(thm)], ['72', '78'])).
% 3.73/3.97  thf('80', plain, ($false),
% 3.73/3.97      inference('simplify_reflect-', [status(thm)], ['70', '79'])).
% 3.73/3.97  
% 3.73/3.97  % SZS output end Refutation
% 3.73/3.97  
% 3.73/3.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
