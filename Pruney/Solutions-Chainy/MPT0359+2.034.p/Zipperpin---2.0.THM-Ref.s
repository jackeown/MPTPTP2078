%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SwMDigs2Si

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 223 expanded)
%              Number of leaves         :   22 (  69 expanded)
%              Depth                    :   17
%              Number of atoms          :  618 (1868 expanded)
%              Number of equality atoms :   63 ( 196 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X29 @ ( k3_subset_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('11',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('12',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('13',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ X0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','25'])).

thf('27',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('34',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['9','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['3','41'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X23: $i] :
      ( ( k1_subset_1 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X23: $i] :
      ( ( k1_subset_1 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X30: $i] :
      ( ( k2_subset_1 @ X30 )
      = ( k3_subset_1 @ X30 @ ( k1_subset_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('50',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('51',plain,(
    ! [X30: $i] :
      ( X30
      = ( k3_subset_1 @ X30 @ ( k1_subset_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('58',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_subset_1 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('63',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['2','61','62'])).

thf('64',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('65',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('66',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','32'])).

thf('68',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SwMDigs2Si
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:41:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 258 iterations in 0.122s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(t39_subset_1, conjecture,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.19/0.54         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i]:
% 0.19/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.19/0.54            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.19/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(involutiveness_k3_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (![X28 : $i, X29 : $i]:
% 0.19/0.54         (((k3_subset_1 @ X29 @ (k3_subset_1 @ X29 @ X28)) = (X28))
% 0.19/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.19/0.54      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.54  thf(d3_tarski, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.54  thf('3', plain,
% 0.19/0.54      (![X1 : $i, X3 : $i]:
% 0.19/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.19/0.54        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.19/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.19/0.54      inference('split', [status(esa)], ['4'])).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.54          | (r2_hidden @ X0 @ X2)
% 0.19/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          ((r2_hidden @ X0 @ sk_B)
% 0.19/0.54           | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.19/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.19/0.54        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.19/0.54       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.19/0.54      inference('split', [status(esa)], ['8'])).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X1 : $i, X3 : $i]:
% 0.19/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.54  thf('11', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.19/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.54  thf('12', plain,
% 0.19/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('split', [status(esa)], ['4'])).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.54  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.19/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.54  thf(d5_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (![X25 : $i, X26 : $i]:
% 0.19/0.54         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.19/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.19/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.54  thf(d5_xboole_0, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.54       ( ![D:$i]:
% 0.19/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X8 @ X7)
% 0.19/0.54          | (r2_hidden @ X8 @ X5)
% 0.19/0.54          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.54         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A))
% 0.19/0.54           | (r2_hidden @ X0 @ sk_A)))
% 0.19/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['17', '19'])).
% 0.19/0.54  thf('21', plain,
% 0.19/0.54      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.19/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X8 @ X7)
% 0.19/0.54          | ~ (r2_hidden @ X8 @ X6)
% 0.19/0.54          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X8 @ X6)
% 0.19/0.54          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A))
% 0.19/0.54           | ~ (r2_hidden @ X0 @ sk_A)))
% 0.19/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['21', '23'])).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A)))
% 0.19/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('clc', [status(thm)], ['20', '24'])).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      ((![X0 : $i]: (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ X0))
% 0.19/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['10', '25'])).
% 0.19/0.54  thf('27', plain,
% 0.19/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.54  thf('28', plain,
% 0.19/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.19/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.19/0.54      inference('split', [status(esa)], ['8'])).
% 0.19/0.54  thf('29', plain,
% 0.19/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.19/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.19/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.54  thf('30', plain,
% 0.19/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.19/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.19/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.19/0.54       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['26', '31'])).
% 0.19/0.54  thf('33', plain,
% 0.19/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.19/0.54       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.19/0.54      inference('split', [status(esa)], ['4'])).
% 0.19/0.54  thf('34', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.19/0.54      inference('sat_resolution*', [status(thm)], ['9', '32', '33'])).
% 0.19/0.54  thf('35', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((r2_hidden @ X0 @ sk_B)
% 0.19/0.54          | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.54      inference('simpl_trail', [status(thm)], ['7', '34'])).
% 0.19/0.54  thf('36', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('37', plain,
% 0.19/0.54      (![X25 : $i, X26 : $i]:
% 0.19/0.54         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.19/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.54  thf('38', plain,
% 0.19/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.54  thf('39', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X8 @ X6)
% 0.19/0.54          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.54  thf('40', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.54          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.54  thf('41', plain,
% 0.19/0.54      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.19/0.54      inference('clc', [status(thm)], ['35', '40'])).
% 0.19/0.54  thf('42', plain,
% 0.19/0.54      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)),
% 0.19/0.54      inference('sup-', [status(thm)], ['3', '41'])).
% 0.19/0.54  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.54  thf('43', plain, (![X23 : $i]: ((k1_subset_1 @ X23) = (k1_xboole_0))),
% 0.19/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.54  thf('44', plain,
% 0.19/0.54      (![X1 : $i, X3 : $i]:
% 0.19/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.54  thf(t4_subset_1, axiom,
% 0.19/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.54  thf('45', plain,
% 0.19/0.54      (![X31 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.19/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.54  thf('46', plain,
% 0.19/0.54      (![X25 : $i, X26 : $i]:
% 0.19/0.54         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.19/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.19/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.54  thf('47', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.54  thf('48', plain, (![X23 : $i]: ((k1_subset_1 @ X23) = (k1_xboole_0))),
% 0.19/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.54  thf(t22_subset_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.19/0.54  thf('49', plain,
% 0.19/0.54      (![X30 : $i]:
% 0.19/0.54         ((k2_subset_1 @ X30) = (k3_subset_1 @ X30 @ (k1_subset_1 @ X30)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.19/0.54  thf('50', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.19/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.54  thf('51', plain,
% 0.19/0.54      (![X30 : $i]: ((X30) = (k3_subset_1 @ X30 @ (k1_subset_1 @ X30)))),
% 0.19/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.54  thf('52', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.19/0.54      inference('sup+', [status(thm)], ['48', '51'])).
% 0.19/0.54  thf('53', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.54      inference('demod', [status(thm)], ['47', '52'])).
% 0.19/0.54  thf('54', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X8 @ X6)
% 0.19/0.54          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.54  thf('55', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.54  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.54      inference('condensation', [status(thm)], ['55'])).
% 0.19/0.54  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.54      inference('sup-', [status(thm)], ['44', '56'])).
% 0.19/0.54  thf(d10_xboole_0, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.54  thf('58', plain,
% 0.19/0.54      (![X10 : $i, X12 : $i]:
% 0.19/0.54         (((X10) = (X12))
% 0.19/0.54          | ~ (r1_tarski @ X12 @ X10)
% 0.19/0.54          | ~ (r1_tarski @ X10 @ X12))),
% 0.19/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.54  thf('59', plain,
% 0.19/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.54  thf('60', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X1 @ (k1_subset_1 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['43', '59'])).
% 0.19/0.54  thf('61', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['42', '60'])).
% 0.19/0.54  thf('62', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.19/0.54      inference('sup+', [status(thm)], ['48', '51'])).
% 0.19/0.54  thf('63', plain, (((sk_A) = (sk_B))),
% 0.19/0.54      inference('demod', [status(thm)], ['2', '61', '62'])).
% 0.19/0.54  thf('64', plain,
% 0.19/0.54      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.19/0.54         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('split', [status(esa)], ['8'])).
% 0.19/0.54  thf('65', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.19/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.54  thf('66', plain,
% 0.19/0.54      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.19/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.54  thf('67', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.19/0.54      inference('sat_resolution*', [status(thm)], ['9', '32'])).
% 0.19/0.54  thf('68', plain, (((sk_B) != (sk_A))),
% 0.19/0.54      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 0.19/0.54  thf('69', plain, ($false),
% 0.19/0.54      inference('simplify_reflect-', [status(thm)], ['63', '68'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
