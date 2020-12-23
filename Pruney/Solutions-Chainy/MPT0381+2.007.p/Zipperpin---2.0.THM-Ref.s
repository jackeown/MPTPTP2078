%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PD19xF3TGe

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 424 expanded)
%              Number of leaves         :   25 ( 141 expanded)
%              Depth                    :   15
%              Number of atoms          :  394 (2810 expanded)
%              Number of equality atoms :   28 ( 165 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_xboole_0 @ X29 )
      | ( m1_subset_1 @ X29 @ X28 )
      | ~ ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t63_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_subset_1])).

thf('1',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( m1_subset_1 @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_A @ sk_B_2 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X33 @ X32 )
      | ( m1_subset_1 @ ( k1_tarski @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','10'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(clc,[status(thm)],['8','9'])).

thf('26',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X26 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ~ ( v1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( sk_A = X1 ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X25 )
      | ~ ( r2_hidden @ X23 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('39',plain,(
    ! [X24: $i,X25: $i] :
      ~ ( r2_hidden @ X25 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X1: $i] : ( sk_A = X1 ) ),
    inference(demod,[status(thm)],['33','43'])).

thf('45',plain,(
    ! [X1: $i] : ( sk_A = X1 ) ),
    inference(demod,[status(thm)],['33','43'])).

thf('46',plain,(
    ~ ( m1_subset_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['11','44','45'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('50',plain,(
    ! [X1: $i] : ( sk_A = X1 ) ),
    inference(demod,[status(thm)],['33','43'])).

thf('51',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['48','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PD19xF3TGe
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 86 iterations in 0.040s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(d2_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X28 : $i, X29 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ X29)
% 0.21/0.49          | (m1_subset_1 @ X29 @ X28)
% 0.21/0.49          | ~ (v1_xboole_0 @ X28))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.49  thf(t63_subset_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain, ((r2_hidden @ sk_A @ sk_B_2)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X27 : $i, X28 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X27 @ X28)
% 0.21/0.49          | (m1_subset_1 @ X27 @ X28)
% 0.21/0.49          | (v1_xboole_0 @ X28))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X27 : $i, X28 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.21/0.49      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((m1_subset_1 @ sk_A @ sk_B_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf(t55_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.49       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X32 : $i, X33 : $i]:
% 0.21/0.49         (((X32) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ X33 @ X32)
% 0.21/0.49          | (m1_subset_1 @ (k1_tarski @ X33) @ (k1_zfmisc_1 @ X32)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.49        | ((sk_B_2) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.21/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '10'])).
% 0.21/0.49  thf(t4_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X31 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X27 : $i, X28 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X27 @ X28)
% 0.21/0.49          | (r2_hidden @ X27 @ X28)
% 0.21/0.49          | (v1_xboole_0 @ X28))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.21/0.49          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf(fc1_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('15', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.49      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf(d1_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X21 @ X20)
% 0.21/0.49          | (r1_tarski @ X21 @ X19)
% 0.21/0.49          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X19 : $i, X21 : $i]:
% 0.21/0.49         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.49  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.49  thf(t28_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf(t100_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.49           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.49           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((r2_hidden @ sk_A @ sk_B_2)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.21/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('26', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf(t64_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.21/0.49         ((r2_hidden @ X23 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X26)))
% 0.21/0.49          | ((X23) = (X26))
% 0.21/0.49          | ~ (r2_hidden @ X23 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_A) = (X0))
% 0.21/0.49          | (r2_hidden @ sk_A @ (k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_A) = (X0))
% 0.21/0.49          | ~ (v1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.49           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_A) = (X0))
% 0.21/0.49          | ~ (v1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)) | ((sk_A) = (X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.49           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.49           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('37', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.49         (((X23) != (X25))
% 0.21/0.49          | ~ (r2_hidden @ X23 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X25))))),
% 0.21/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         ~ (r2_hidden @ X25 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X25)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ~ (r2_hidden @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '42'])).
% 0.21/0.49  thf('44', plain, (![X1 : $i]: ((sk_A) = (X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '43'])).
% 0.21/0.49  thf('45', plain, (![X1 : $i]: ((sk_A) = (X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '43'])).
% 0.21/0.49  thf('46', plain, (~ (m1_subset_1 @ sk_A @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '44', '45'])).
% 0.21/0.49  thf('47', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '46'])).
% 0.21/0.49  thf('48', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '42'])).
% 0.21/0.49  thf('50', plain, (![X1 : $i]: ((sk_A) = (X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '43'])).
% 0.21/0.49  thf('51', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain, ($false), inference('demod', [status(thm)], ['48', '51'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
