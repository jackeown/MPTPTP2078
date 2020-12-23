%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QjT4DSIlO3

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:35 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 171 expanded)
%              Number of leaves         :   22 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  622 (1590 expanded)
%              Number of equality atoms :   40 ( 120 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26
       != ( k1_wellord2 @ X25 ) )
      | ( ( k3_relat_1 @ X26 )
        = X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X25 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X25 ) )
        = X25 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X25: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X12 @ X9 ) @ ( sk_D @ X12 @ X9 ) ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ X24 )
      | ( r2_hidden @ X22 @ ( k3_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X0 ) )
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X25: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X25: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_wellord2 @ X25 ) )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( r2_hidden @ X28 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ X26 )
      | ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('17',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X25 ) )
      | ~ ( r1_tarski @ X27 @ X28 )
      | ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ ( k1_wellord2 @ X25 ) )
      | ~ ( r2_hidden @ X28 @ X25 )
      | ~ ( r2_hidden @ X27 @ X25 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( r2_hidden @ ( k4_tarski @ X27 @ X28 ) @ ( k1_wellord2 @ X25 ) )
      | ~ ( r2_hidden @ X28 @ X25 )
      | ~ ( r2_hidden @ X27 @ X25 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X9: $i,X12: $i,X13: $i] :
      ( ( X12
        = ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X12 @ X9 ) @ X13 ) @ X9 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X21: $i] :
      ( ( r1_tarski @ X21 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X21 ) @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X25: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19
        = ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X19 @ X16 ) @ ( sk_C_2 @ X19 @ X16 ) ) @ X16 )
      | ( r2_hidden @ ( sk_C_2 @ X19 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ X24 )
      | ( r2_hidden @ X23 @ ( k3_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X0 ) )
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X25: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('39',plain,(
    ! [X25: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i,X19: $i,X20: $i] :
      ( ( X19
        = ( k2_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_C_2 @ X19 @ X16 ) ) @ X16 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X19 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QjT4DSIlO3
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 276 iterations in 0.252s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.50/0.71  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.50/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.71  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.50/0.71  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.50/0.71  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.50/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.50/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.71  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.50/0.71  thf(t33_wellord2, conjecture,
% 0.50/0.71    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(d1_wellord2, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( v1_relat_1 @ B ) =>
% 0.50/0.71       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.50/0.71         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.50/0.71           ( ![C:$i,D:$i]:
% 0.50/0.71             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.50/0.71               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.50/0.71                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      (![X25 : $i, X26 : $i]:
% 0.50/0.71         (((X26) != (k1_wellord2 @ X25))
% 0.50/0.71          | ((k3_relat_1 @ X26) = (X25))
% 0.50/0.71          | ~ (v1_relat_1 @ X26))),
% 0.50/0.71      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (![X25 : $i]:
% 0.50/0.71         (~ (v1_relat_1 @ (k1_wellord2 @ X25))
% 0.50/0.71          | ((k3_relat_1 @ (k1_wellord2 @ X25)) = (X25)))),
% 0.50/0.71      inference('simplify', [status(thm)], ['1'])).
% 0.50/0.71  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.50/0.71  thf('3', plain, (![X29 : $i]: (v1_relat_1 @ (k1_wellord2 @ X29))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.50/0.71  thf('4', plain, (![X25 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X25)) = (X25))),
% 0.50/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf(d4_relat_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.50/0.71       ( ![C:$i]:
% 0.50/0.71         ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.71           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X9 : $i, X12 : $i]:
% 0.50/0.71         (((X12) = (k1_relat_1 @ X9))
% 0.50/0.71          | (r2_hidden @ 
% 0.50/0.71             (k4_tarski @ (sk_C_1 @ X12 @ X9) @ (sk_D @ X12 @ X9)) @ X9)
% 0.50/0.71          | (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.50/0.71      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.50/0.71  thf(t30_relat_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( v1_relat_1 @ C ) =>
% 0.50/0.71       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.50/0.71         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.50/0.71           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         (~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ X24)
% 0.50/0.71          | (r2_hidden @ X22 @ (k3_relat_1 @ X24))
% 0.50/0.71          | ~ (v1_relat_1 @ X24))),
% 0.50/0.71      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.50/0.71          | ((X1) = (k1_relat_1 @ X0))
% 0.50/0.71          | ~ (v1_relat_1 @ X0)
% 0.50/0.71          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_1 @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0))
% 0.50/0.71          | ~ (v1_relat_1 @ X0)
% 0.50/0.71          | ((k3_relat_1 @ X0) = (k1_relat_1 @ X0)))),
% 0.50/0.71      inference('eq_fact', [status(thm)], ['7'])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.50/0.71           (k3_relat_1 @ (k1_wellord2 @ X0)))
% 0.50/0.71          | ((k3_relat_1 @ (k1_wellord2 @ X0))
% 0.50/0.71              = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.50/0.71          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['4', '8'])).
% 0.50/0.71  thf('10', plain, (![X25 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X25)) = (X25))),
% 0.50/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf('11', plain, (![X25 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X25)) = (X25))),
% 0.50/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf('12', plain, (![X29 : $i]: (v1_relat_1 @ (k1_wellord2 @ X29))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.50/0.71          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.50/0.71  thf(d10_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.50/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.71  thf('15', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.50/0.71      inference('simplify', [status(thm)], ['14'])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.71         (((X26) != (k1_wellord2 @ X25))
% 0.50/0.71          | ~ (r2_hidden @ X27 @ X25)
% 0.50/0.71          | ~ (r2_hidden @ X28 @ X25)
% 0.50/0.71          | (r2_hidden @ (k4_tarski @ X27 @ X28) @ X26)
% 0.50/0.71          | ~ (r1_tarski @ X27 @ X28)
% 0.50/0.71          | ~ (v1_relat_1 @ X26))),
% 0.50/0.71      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.50/0.71         (~ (v1_relat_1 @ (k1_wellord2 @ X25))
% 0.50/0.71          | ~ (r1_tarski @ X27 @ X28)
% 0.50/0.71          | (r2_hidden @ (k4_tarski @ X27 @ X28) @ (k1_wellord2 @ X25))
% 0.50/0.71          | ~ (r2_hidden @ X28 @ X25)
% 0.50/0.71          | ~ (r2_hidden @ X27 @ X25))),
% 0.50/0.71      inference('simplify', [status(thm)], ['16'])).
% 0.50/0.71  thf('18', plain, (![X29 : $i]: (v1_relat_1 @ (k1_wellord2 @ X29))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.50/0.71         (~ (r1_tarski @ X27 @ X28)
% 0.50/0.71          | (r2_hidden @ (k4_tarski @ X27 @ X28) @ (k1_wellord2 @ X25))
% 0.50/0.71          | ~ (r2_hidden @ X28 @ X25)
% 0.50/0.71          | ~ (r2_hidden @ X27 @ X25))),
% 0.50/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.50/0.71  thf('20', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.71          | ~ (r2_hidden @ X0 @ X1)
% 0.50/0.71          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['15', '19'])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.50/0.71          | ~ (r2_hidden @ X0 @ X1))),
% 0.50/0.71      inference('simplify', [status(thm)], ['20'])).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.50/0.71          | (r2_hidden @ 
% 0.50/0.71             (k4_tarski @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.50/0.71              (sk_C_1 @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.50/0.71             (k1_wellord2 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['13', '21'])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (![X9 : $i, X12 : $i, X13 : $i]:
% 0.50/0.71         (((X12) = (k1_relat_1 @ X9))
% 0.50/0.71          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X12 @ X9) @ X13) @ X9)
% 0.50/0.71          | ~ (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.50/0.71      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.50/0.71  thf('24', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.50/0.71          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.50/0.71          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.50/0.71          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('simplify', [status(thm)], ['24'])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.50/0.71          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.50/0.71  thf('27', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.50/0.71      inference('clc', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf(t21_relat_1, axiom,
% 0.50/0.71    (![A:$i]:
% 0.50/0.71     ( ( v1_relat_1 @ A ) =>
% 0.50/0.71       ( r1_tarski @
% 0.50/0.71         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      (![X21 : $i]:
% 0.50/0.71         ((r1_tarski @ X21 @ 
% 0.50/0.71           (k2_zfmisc_1 @ (k1_relat_1 @ X21) @ (k2_relat_1 @ X21)))
% 0.50/0.71          | ~ (v1_relat_1 @ X21))),
% 0.50/0.71      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.50/0.71           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))
% 0.50/0.71          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['27', '28'])).
% 0.50/0.71  thf('30', plain, (![X29 : $i]: (v1_relat_1 @ (k1_wellord2 @ X29))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.50/0.71          (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.50/0.71  thf('32', plain, (![X25 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X25)) = (X25))),
% 0.50/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf(d5_relat_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.50/0.71       ( ![C:$i]:
% 0.50/0.71         ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.71           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (![X16 : $i, X19 : $i]:
% 0.50/0.71         (((X19) = (k2_relat_1 @ X16))
% 0.50/0.71          | (r2_hidden @ 
% 0.50/0.71             (k4_tarski @ (sk_D_2 @ X19 @ X16) @ (sk_C_2 @ X19 @ X16)) @ X16)
% 0.50/0.71          | (r2_hidden @ (sk_C_2 @ X19 @ X16) @ X19))),
% 0.50/0.71      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.50/0.71  thf('34', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.71         (~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ X24)
% 0.50/0.71          | (r2_hidden @ X23 @ (k3_relat_1 @ X24))
% 0.50/0.71          | ~ (v1_relat_1 @ X24))),
% 0.50/0.71      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.50/0.71          | ((X1) = (k2_relat_1 @ X0))
% 0.50/0.71          | ~ (v1_relat_1 @ X0)
% 0.50/0.71          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.71  thf('36', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_2 @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0))
% 0.50/0.71          | ~ (v1_relat_1 @ X0)
% 0.50/0.71          | ((k3_relat_1 @ X0) = (k2_relat_1 @ X0)))),
% 0.50/0.71      inference('eq_fact', [status(thm)], ['35'])).
% 0.50/0.71  thf('37', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.50/0.71           (k3_relat_1 @ (k1_wellord2 @ X0)))
% 0.50/0.71          | ((k3_relat_1 @ (k1_wellord2 @ X0))
% 0.50/0.71              = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.50/0.71          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['32', '36'])).
% 0.50/0.71  thf('38', plain, (![X25 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X25)) = (X25))),
% 0.50/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf('39', plain, (![X25 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X25)) = (X25))),
% 0.50/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf('40', plain, (![X29 : $i]: (v1_relat_1 @ (k1_wellord2 @ X29))),
% 0.50/0.71      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.50/0.71  thf('41', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.50/0.71          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.50/0.71  thf('42', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.50/0.71          | ~ (r2_hidden @ X0 @ X1))),
% 0.50/0.71      inference('simplify', [status(thm)], ['20'])).
% 0.50/0.71  thf('43', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.50/0.71          | (r2_hidden @ 
% 0.50/0.71             (k4_tarski @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ 
% 0.50/0.71              (sk_C_2 @ X0 @ (k1_wellord2 @ X0))) @ 
% 0.50/0.71             (k1_wellord2 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      (![X16 : $i, X19 : $i, X20 : $i]:
% 0.50/0.71         (((X19) = (k2_relat_1 @ X16))
% 0.50/0.71          | ~ (r2_hidden @ (k4_tarski @ X20 @ (sk_C_2 @ X19 @ X16)) @ X16)
% 0.50/0.71          | ~ (r2_hidden @ (sk_C_2 @ X19 @ X16) @ X19))),
% 0.50/0.71      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.50/0.71  thf('45', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.50/0.71          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.50/0.71          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.71  thf('46', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.50/0.71          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('simplify', [status(thm)], ['45'])).
% 0.50/0.71  thf('47', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ (sk_C_2 @ X0 @ (k1_wellord2 @ X0)) @ X0)
% 0.50/0.71          | ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.50/0.71      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.50/0.71  thf('48', plain, (![X0 : $i]: ((X0) = (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.50/0.71      inference('clc', [status(thm)], ['46', '47'])).
% 0.50/0.71  thf('49', plain,
% 0.50/0.71      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['31', '48'])).
% 0.50/0.71  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
