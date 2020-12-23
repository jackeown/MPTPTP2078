%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3F90gGEvXR

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 164 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  557 (1345 expanded)
%              Number of equality atoms :   49 ( 127 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['12'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('19',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('27',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf('33',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('36',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['24','34','35'])).

thf('37',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['22','36'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    | ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('43',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['46','51'])).

thf('53',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','52'])).

thf('54',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('55',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('56',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['24','34'])).

thf('58',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3F90gGEvXR
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 174 iterations in 0.099s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(d5_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.57       ( ![D:$i]:
% 0.22/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.22/0.57         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.22/0.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.22/0.57          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.22/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.57  thf(t7_xboole_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.57          | (r2_hidden @ X4 @ X1)
% 0.22/0.57          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.57         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.57          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '3'])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.57          | ~ (r2_hidden @ X4 @ X2)
% 0.22/0.57          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.57          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.57          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.22/0.57          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '8'])).
% 0.22/0.57  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.57          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.57  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.57      inference('condensation', [status(thm)], ['12'])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.22/0.57          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '13'])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.57          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '3'])).
% 0.22/0.57  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.57      inference('condensation', [status(thm)], ['12'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.22/0.57          | ((X1) = (k1_xboole_0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['14', '17'])).
% 0.22/0.57  thf(t38_subset_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.57         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i]:
% 0.22/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.57            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.22/0.57        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('20', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      ((((sk_B_1) = (k1_xboole_0))
% 0.22/0.57        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.22/0.57         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.22/0.57      inference('split', [status(esa)], ['21'])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.22/0.57        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.22/0.57       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('split', [status(esa)], ['23'])).
% 0.22/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.57  thf('25', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf('26', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.22/0.57        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.22/0.57         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.57      inference('split', [status(esa)], ['27'])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['26', '28'])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.22/0.57         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.22/0.57      inference('split', [status(esa)], ['23'])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.57         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.22/0.57             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['26', '28'])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.57         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.22/0.57             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.22/0.57       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['25', '33'])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.22/0.57       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.22/0.57      inference('split', [status(esa)], ['27'])).
% 0.22/0.57  thf('36', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('sat_resolution*', [status(thm)], ['24', '34', '35'])).
% 0.22/0.57  thf('37', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.22/0.57      inference('simpl_trail', [status(thm)], ['22', '36'])).
% 0.22/0.57  thf(d1_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X10 @ X11)
% 0.22/0.57          | (r2_hidden @ X10 @ X12)
% 0.22/0.57          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i]:
% 0.22/0.57         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.22/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.57  thf('40', plain,
% 0.22/0.57      ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['37', '39'])).
% 0.22/0.57  thf(d2_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      (![X15 : $i, X16 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X15 @ X16)
% 0.22/0.57          | (m1_subset_1 @ X15 @ X16)
% 0.22/0.57          | (v1_xboole_0 @ X16))),
% 0.22/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.22/0.57        | (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.57  thf(fc1_subset_1, axiom,
% 0.22/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.57  thf('43', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.57      inference('clc', [status(thm)], ['42', '43'])).
% 0.22/0.57  thf(l3_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X22 @ X23)
% 0.22/0.57          | (r2_hidden @ X22 @ X24)
% 0.22/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.22/0.57          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.57  thf('47', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d5_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('48', plain,
% 0.22/0.57      (![X19 : $i, X20 : $i]:
% 0.22/0.57         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.22/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.57  thf('49', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.57  thf('50', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.57          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('51', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.22/0.57          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.57  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.22/0.57      inference('clc', [status(thm)], ['46', '51'])).
% 0.22/0.57  thf('53', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['18', '52'])).
% 0.22/0.57  thf('54', plain,
% 0.22/0.57      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.22/0.57         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.57      inference('split', [status(esa)], ['23'])).
% 0.22/0.57  thf('55', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.57  thf('56', plain,
% 0.22/0.57      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.57  thf('57', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.22/0.57      inference('sat_resolution*', [status(thm)], ['24', '34'])).
% 0.22/0.57  thf('58', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.57      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.22/0.57  thf('59', plain, ($false),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['53', '58'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
