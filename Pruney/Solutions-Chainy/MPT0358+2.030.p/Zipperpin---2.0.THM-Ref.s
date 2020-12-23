%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WoPhh4HDaV

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:25 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 151 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  400 (1149 expanded)
%              Number of equality atoms :   39 ( 101 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k3_subset_1 @ X64 @ X65 )
        = ( k4_xboole_0 @ X64 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X20: $i] :
      ( ( r1_xboole_0 @ X20 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('10',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['9'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X63: $i] :
      ( ( k1_subset_1 @ X63 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('25',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('30',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ~ ( v1_xboole_0 @ X0 )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','34','35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['6','36'])).

thf('38',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','37'])).

thf('39',plain,(
    ! [X63: $i] :
      ( ( k1_subset_1 @ X63 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('40',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('41',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['8','34'])).

thf('43',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WoPhh4HDaV
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:57:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 404 iterations in 0.152s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.44/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.44/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.61  thf(t38_subset_1, conjecture,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.61       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.44/0.61         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i,B:$i]:
% 0.44/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.61          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.44/0.61            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.44/0.61  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(d5_subset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      (![X64 : $i, X65 : $i]:
% 0.44/0.61         (((k3_subset_1 @ X64 @ X65) = (k4_xboole_0 @ X64 @ X65))
% 0.44/0.61          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.61  thf(t38_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.44/0.61       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      (![X12 : $i, X13 : $i]:
% 0.44/0.61         (((X12) = (k1_xboole_0))
% 0.44/0.61          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.44/0.61        | ((sk_B) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.61  thf('5', plain,
% 0.44/0.61      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.44/0.61        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.44/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.44/0.61      inference('split', [status(esa)], ['5'])).
% 0.44/0.61  thf('7', plain,
% 0.44/0.61      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.44/0.61        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.44/0.61       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('split', [status(esa)], ['7'])).
% 0.44/0.61  thf(t66_xboole_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.44/0.61       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      (![X20 : $i]: ((r1_xboole_0 @ X20 @ X20) | ((X20) != (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.44/0.61  thf('10', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.44/0.61      inference('simplify', [status(thm)], ['9'])).
% 0.44/0.61  thf(t69_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.61       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.44/0.61  thf('11', plain,
% 0.44/0.61      (![X22 : $i, X23 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X22 @ X23)
% 0.44/0.61          | ~ (r1_tarski @ X22 @ X23)
% 0.44/0.61          | (v1_xboole_0 @ X22))),
% 0.44/0.61      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.61  thf(d3_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      (![X3 : $i, X5 : $i]:
% 0.44/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf('14', plain,
% 0.44/0.61      (![X3 : $i, X5 : $i]:
% 0.44/0.61         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.44/0.61  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.61      inference('demod', [status(thm)], ['12', '16'])).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (![X3 : $i, X5 : $i]:
% 0.44/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf(t7_boole, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (![X24 : $i, X25 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X24 @ X25) | ~ (v1_xboole_0 @ X25))),
% 0.44/0.61      inference('cnf', [status(esa)], [t7_boole])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.61  thf('21', plain,
% 0.44/0.61      (![X12 : $i, X13 : $i]:
% 0.44/0.61         (((X12) = (k1_xboole_0))
% 0.44/0.61          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.61  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.44/0.61  thf('24', plain, (![X63 : $i]: ((k1_subset_1 @ X63) = (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.44/0.61  thf('25', plain,
% 0.44/0.61      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('split', [status(esa)], ['5'])).
% 0.44/0.61  thf('26', plain,
% 0.44/0.61      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['24', '25'])).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.44/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.44/0.61      inference('split', [status(esa)], ['7'])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.44/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.44/0.61             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('sup+', [status(thm)], ['24', '25'])).
% 0.44/0.61  thf('30', plain,
% 0.44/0.61      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.44/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.44/0.61             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.44/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.44/0.61             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['23', '30'])).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      ((![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0)))
% 0.44/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.44/0.61             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['22', '31'])).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      ((![X0 : $i]: ~ (v1_xboole_0 @ X0))
% 0.44/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.44/0.61             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('simplify', [status(thm)], ['32'])).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.44/0.61       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['17', '33'])).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.44/0.61       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.44/0.61      inference('split', [status(esa)], ['5'])).
% 0.44/0.61  thf('36', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('sat_resolution*', [status(thm)], ['8', '34', '35'])).
% 0.44/0.61  thf('37', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['6', '36'])).
% 0.44/0.61  thf('38', plain, (((sk_B) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['4', '37'])).
% 0.44/0.61  thf('39', plain, (![X63 : $i]: ((k1_subset_1 @ X63) = (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.44/0.61  thf('40', plain,
% 0.44/0.61      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.44/0.61         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('split', [status(esa)], ['7'])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.61  thf('42', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.44/0.61      inference('sat_resolution*', [status(thm)], ['8', '34'])).
% 0.44/0.61  thf('43', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.61      inference('simpl_trail', [status(thm)], ['41', '42'])).
% 0.44/0.61  thf('44', plain, ($false),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['38', '43'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
