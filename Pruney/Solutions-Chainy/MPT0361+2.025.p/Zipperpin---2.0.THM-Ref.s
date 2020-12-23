%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rL9Ppk0Gch

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:53 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 114 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  556 (1229 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k4_subset_1 @ X44 @ X43 @ X45 )
        = ( k2_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ ( k3_tarski @ X33 ) )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( r1_tarski @ X3 @ ( k3_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X39 @ X38 @ X40 ) @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('26',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( r1_tarski @ X46 @ ( k3_subset_1 @ X47 @ X48 ) )
      | ~ ( r1_tarski @ X48 @ ( k3_subset_1 @ X47 @ X46 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('30',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_subset_1 @ X42 @ ( k3_subset_1 @ X42 @ X41 ) )
        = X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) )
    = ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('33',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['6','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rL9Ppk0Gch
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 601 iterations in 0.506s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.96  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.75/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.96  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.75/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.96  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.96  thf(t41_subset_1, conjecture,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.96       ( ![C:$i]:
% 0.75/0.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.96           ( r1_tarski @
% 0.75/0.96             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.75/0.96             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.96    (~( ![A:$i,B:$i]:
% 0.75/0.96        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.96          ( ![C:$i]:
% 0.75/0.96            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.96              ( r1_tarski @
% 0.75/0.96                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.75/0.96                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 0.75/0.96  thf('0', plain,
% 0.75/0.96      (~ (r1_tarski @ 
% 0.75/0.96          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.75/0.96          (k3_subset_1 @ sk_A @ sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(redefinition_k4_subset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.96       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.75/0.96  thf('3', plain,
% 0.75/0.96      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.75/0.96          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44))
% 0.75/0.96          | ((k4_subset_1 @ X44 @ X43 @ X45) = (k2_xboole_0 @ X43 @ X45)))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '4'])).
% 0.75/0.96  thf('6', plain,
% 0.75/0.96      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.75/0.96          (k3_subset_1 @ sk_A @ sk_B))),
% 0.75/0.96      inference('demod', [status(thm)], ['0', '5'])).
% 0.75/0.96  thf(t70_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.96  thf('7', plain,
% 0.75/0.96      (![X12 : $i, X13 : $i]:
% 0.75/0.96         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.75/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.96  thf(d1_enumset1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.96           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.96  thf(zf_stmt_2, axiom,
% 0.75/0.96    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.96     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.96       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_3, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.96  thf('8', plain,
% 0.75/0.96      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.75/0.96          | (r2_hidden @ X5 @ X9)
% 0.75/0.96          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.96  thf('9', plain,
% 0.75/0.96      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.75/0.96         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.75/0.96          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.75/0.96      inference('simplify', [status(thm)], ['8'])).
% 0.75/0.96  thf(l49_zfmisc_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.75/0.96  thf('10', plain,
% 0.75/0.96      (![X32 : $i, X33 : $i]:
% 0.75/0.96         ((r1_tarski @ X32 @ (k3_tarski @ X33)) | ~ (r2_hidden @ X32 @ X33))),
% 0.75/0.96      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.75/0.96  thf('11', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.75/0.96          | (r1_tarski @ X3 @ (k3_tarski @ (k1_enumset1 @ X2 @ X1 @ X0))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.96  thf('12', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((r1_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 0.75/0.96          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.96      inference('sup+', [status(thm)], ['7', '11'])).
% 0.75/0.96  thf(l51_zfmisc_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.96  thf('13', plain,
% 0.75/0.96      (![X34 : $i, X35 : $i]:
% 0.75/0.96         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 0.75/0.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/0.96  thf('14', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.96          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.96      inference('demod', [status(thm)], ['12', '13'])).
% 0.75/0.96  thf('15', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.96         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.96  thf('16', plain,
% 0.75/0.96      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.75/0.96      inference('simplify', [status(thm)], ['15'])).
% 0.75/0.96  thf('17', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['14', '16'])).
% 0.75/0.96  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(dt_k4_subset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.96       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.96  thf('20', plain,
% 0.75/0.96      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.75/0.96          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 0.75/0.96          | (m1_subset_1 @ (k4_subset_1 @ X39 @ X38 @ X40) @ 
% 0.75/0.96             (k1_zfmisc_1 @ X39)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.75/0.96  thf('21', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.75/0.96           (k1_zfmisc_1 @ sk_A))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.96  thf('22', plain,
% 0.75/0.96      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('sup-', [status(thm)], ['18', '21'])).
% 0.75/0.96  thf(dt_k3_subset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.96       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.96  thf('23', plain,
% 0.75/0.96      (![X36 : $i, X37 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k3_subset_1 @ X36 @ X37) @ (k1_zfmisc_1 @ X36))
% 0.75/0.96          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.75/0.96  thf('24', plain,
% 0.75/0.96      ((m1_subset_1 @ 
% 0.75/0.96        (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.75/0.96        (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.96  thf('25', plain,
% 0.75/0.96      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '4'])).
% 0.75/0.96  thf('26', plain,
% 0.75/0.96      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.75/0.96        (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.96  thf(t35_subset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.96       ( ![C:$i]:
% 0.75/0.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.96           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.75/0.96             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.75/0.96  thf('27', plain,
% 0.75/0.96      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.75/0.96          | (r1_tarski @ X46 @ (k3_subset_1 @ X47 @ X48))
% 0.75/0.96          | ~ (r1_tarski @ X48 @ (k3_subset_1 @ X47 @ X46))
% 0.75/0.96          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.75/0.96  thf('28', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.96          | ~ (r1_tarski @ X0 @ 
% 0.75/0.96               (k3_subset_1 @ sk_A @ 
% 0.75/0.96                (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))
% 0.75/0.96          | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.75/0.96             (k3_subset_1 @ sk_A @ X0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['26', '27'])).
% 0.75/0.96  thf('29', plain,
% 0.75/0.96      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('sup-', [status(thm)], ['18', '21'])).
% 0.75/0.96  thf(involutiveness_k3_subset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.96       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.75/0.96  thf('30', plain,
% 0.75/0.96      (![X41 : $i, X42 : $i]:
% 0.75/0.96         (((k3_subset_1 @ X42 @ (k3_subset_1 @ X42 @ X41)) = (X41))
% 0.75/0.96          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.75/0.96      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.75/0.96  thf('31', plain,
% 0.75/0.96      (((k3_subset_1 @ sk_A @ 
% 0.75/0.96         (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)))
% 0.75/0.96         = (k4_subset_1 @ sk_A @ sk_B @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.96  thf('32', plain,
% 0.75/0.96      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '4'])).
% 0.75/0.96  thf('33', plain,
% 0.75/0.96      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '4'])).
% 0.75/0.96  thf('34', plain,
% 0.75/0.96      (((k3_subset_1 @ sk_A @ 
% 0.75/0.96         (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 0.75/0.96         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.96      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.75/0.96  thf('35', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.96          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.75/0.96          | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.75/0.96             (k3_subset_1 @ sk_A @ X0)))),
% 0.75/0.96      inference('demod', [status(thm)], ['28', '34'])).
% 0.75/0.96  thf('36', plain,
% 0.75/0.96      (((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.75/0.96         (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.96        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['17', '35'])).
% 0.75/0.96  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('38', plain,
% 0.75/0.96      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.75/0.96        (k3_subset_1 @ sk_A @ sk_B))),
% 0.75/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.75/0.96  thf('39', plain, ($false), inference('demod', [status(thm)], ['6', '38'])).
% 0.75/0.96  
% 0.75/0.96  % SZS output end Refutation
% 0.75/0.96  
% 0.75/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
