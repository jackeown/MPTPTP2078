%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JLeVaTA7Lf

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 166 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   21
%              Number of atoms          :  686 (1910 expanded)
%              Number of equality atoms :   67 ( 214 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_tarski @ X3 @ X0 ) )
      | ( ( sk_D @ X5 @ X0 @ X3 )
        = X0 )
      | ( ( sk_D @ X5 @ X0 @ X3 )
        = X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X0 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

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

thf('1',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k11_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ X16 @ ( k1_tarski @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('7',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k11_relat_1 @ X20 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = X0 )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = X1 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k2_tarski @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k2_tarski @ X0 @ X1 ) )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = X1 )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k2_tarski @ X0 @ X1 ) )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = X1 )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = X0 )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X0 )
        = X1 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k2_tarski @ X1 @ X1 ) )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X1 )
        = X1 )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X1 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X1 )
        = X1 )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X1 @ X1 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ X0 @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_tarski @ X3 @ X0 ) )
      | ( ( sk_D @ X5 @ X0 @ X3 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X0 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('29',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('32',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( X24
       != ( k1_funct_1 @ X23 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( k1_funct_1 @ X23 @ X22 ) ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X20 )
      | ( r2_hidden @ X19 @ ( k11_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('46',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( sk_D @ ( k2_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('48',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_A )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','46','47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JLeVaTA7Lf
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:33:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 61 iterations in 0.049s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(d2_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.51       ( ![D:$i]:
% 0.22/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X0 : $i, X3 : $i, X5 : $i]:
% 0.22/0.51         (((X5) = (k2_tarski @ X3 @ X0))
% 0.22/0.51          | ((sk_D @ X5 @ X0 @ X3) = (X0))
% 0.22/0.51          | ((sk_D @ X5 @ X0 @ X3) = (X3))
% 0.22/0.51          | (r2_hidden @ (sk_D @ X5 @ X0 @ X3) @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.51  thf(t14_funct_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.51       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.22/0.51         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.51          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.22/0.51            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.22/0.51  thf('1', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t146_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X18 : $i]:
% 0.22/0.51         (((k9_relat_1 @ X18 @ (k1_relat_1 @ X18)) = (k2_relat_1 @ X18))
% 0.22/0.51          | ~ (v1_relat_1 @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.22/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf(d16_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X16 : $i, X17 : $i]:
% 0.22/0.51         (((k11_relat_1 @ X16 @ X17) = (k9_relat_1 @ X16 @ (k1_tarski @ X17)))
% 0.22/0.51          | ~ (v1_relat_1 @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.22/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf(t204_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ C ) =>
% 0.22/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.51         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X19 @ (k11_relat_1 @ X20 @ X21))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X21 @ X19) @ X20)
% 0.22/0.51          | ~ (v1_relat_1 @ X20))),
% 0.22/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.22/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0) = (X0))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0) = (X1))
% 0.22/0.51          | ((k2_relat_1 @ sk_B) = (k2_tarski @ X0 @ X1))
% 0.22/0.51          | (r2_hidden @ 
% 0.22/0.51             (k4_tarski @ sk_A @ (sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0)) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '13'])).
% 0.22/0.51  thf(t8_funct_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.51           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.22/0.51          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 0.22/0.51          | ~ (v1_funct_1 @ X23)
% 0.22/0.51          | ~ (v1_relat_1 @ X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((k2_relat_1 @ sk_B) = (k2_tarski @ X0 @ X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0) = (X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0) = (X0))
% 0.22/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0)
% 0.22/0.51              = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((k2_relat_1 @ sk_B) = (k2_tarski @ X0 @ X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0) = (X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0) = (X0))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0)
% 0.22/0.51              = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((X0) != (X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0)
% 0.22/0.51              = (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X0) = (X1))
% 0.22/0.51          | ((k2_relat_1 @ sk_B) = (k2_tarski @ X0 @ X1)))),
% 0.22/0.51      inference('eq_fact', [status(thm)], ['19'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X1 : $i]:
% 0.22/0.51         (((k2_relat_1 @ sk_B) = (k2_tarski @ X1 @ X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X1) = (X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X1)
% 0.22/0.51              = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('22', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X1 : $i]:
% 0.22/0.51         (((k2_relat_1 @ sk_B) = (k1_tarski @ X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X1) = (X1))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X1 @ X1)
% 0.22/0.51              = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.22/0.51          | ((sk_D @ (k2_relat_1 @ sk_B) @ X0 @ X0) = (X0))
% 0.22/0.51          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.22/0.51      inference('eq_fact', [status(thm)], ['23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      ((((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.22/0.51        | ((sk_D @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.22/0.51            (k1_funct_1 @ sk_B @ sk_A)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (((sk_D @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.22/0.51         (k1_funct_1 @ sk_B @ sk_A)) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X0 : $i, X3 : $i, X5 : $i]:
% 0.22/0.51         (((X5) = (k2_tarski @ X3 @ X0))
% 0.22/0.51          | ((sk_D @ X5 @ X0 @ X3) != (X0))
% 0.22/0.51          | ~ (r2_hidden @ (sk_D @ X5 @ X0 @ X3) @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      ((~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.22/0.51        | ((sk_D @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.22/0.51            (k1_funct_1 @ sk_B @ sk_A)) != (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51        | ((k2_relat_1 @ sk_B)
% 0.22/0.51            = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.22/0.51               (k1_funct_1 @ sk_B @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('30', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (((X1) != (X0))
% 0.22/0.51          | (r2_hidden @ X1 @ X2)
% 0.22/0.51          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.51  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['30', '32'])).
% 0.22/0.51  thf('34', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.22/0.51          | ((X24) != (k1_funct_1 @ X23 @ X22))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.22/0.51          | ~ (v1_funct_1 @ X23)
% 0.22/0.51          | ~ (v1_relat_1 @ X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X23)
% 0.22/0.51          | ~ (v1_funct_1 @ X23)
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X22 @ (k1_funct_1 @ X23 @ X22)) @ X23)
% 0.22/0.51          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_B @ X0)) @ sk_B)
% 0.22/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.51          | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['34', '36'])).
% 0.22/0.51  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_B @ X0)) @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['33', '40'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_tarski @ X21 @ X19) @ X20)
% 0.22/0.51          | (r2_hidden @ X19 @ (k11_relat_1 @ X20 @ X21))
% 0.22/0.51          | ~ (v1_relat_1 @ X20))),
% 0.22/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.51        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.51  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('45', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (((sk_D @ (k2_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.22/0.51         (k1_funct_1 @ sk_B @ sk_A)) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('48', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      ((((k1_funct_1 @ sk_B @ sk_A) != (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '46', '47', '48'])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      (((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('52', plain, ($false),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
