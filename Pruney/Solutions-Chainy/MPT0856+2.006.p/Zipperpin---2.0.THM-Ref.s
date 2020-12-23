%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SGsZ7iAygc

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 (  97 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  430 ( 640 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t12_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X51 ) @ X52 )
      | ~ ( r2_hidden @ X51 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('3',plain,(
    ! [X40: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X35: $i] :
      ( r1_tarski @ X35 @ ( k1_zfmisc_1 @ ( k3_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X44: $i,X45: $i] :
      ( ( m1_subset_1 @ X44 @ X45 )
      | ~ ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('10',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
    | ( sk_B
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X51 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('19',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['15'])).

thf('23',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['16','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','24'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X42 ) @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('27',plain,(
    ! [X41: $i] :
      ( ( k2_subset_1 @ X41 )
      = X41 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X43: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('33',plain,(
    ! [X27: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X27 ) @ X29 )
        = ( k1_tarski @ X27 ) )
      | ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X44: $i,X45: $i] :
      ( ( m1_subset_1 @ X44 @ X45 )
      | ~ ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['25','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SGsZ7iAygc
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:09:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 95 iterations in 0.042s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(t12_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.20/0.48       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.20/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.20/0.48          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.20/0.48            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t12_mcart_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t10_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_mcart_1 @ X51) @ X52)
% 0.20/0.48          | ~ (r2_hidden @ X51 @ (k2_zfmisc_1 @ X52 @ X53)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('2', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t31_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.48  thf('3', plain, (![X40 : $i]: ((k3_tarski @ (k1_tarski @ X40)) = (X40))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.48  thf(t100_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X35 : $i]: (r1_tarski @ X35 @ (k1_zfmisc_1 @ (k3_tarski @ X35)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | (r2_hidden @ X0 @ X2)
% 0.20/0.48          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.20/0.48          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.48  thf(t1_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X44 : $i, X45 : $i]:
% 0.20/0.48         ((m1_subset_1 @ X44 @ X45) | ~ (r2_hidden @ X44 @ X45))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_mcart_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(t3_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X48 : $i, X49 : $i]:
% 0.20/0.48         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('12', plain, ((r1_tarski @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X8 : $i, X10 : $i]:
% 0.20/0.48         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_B @ (k1_mcart_1 @ sk_A))
% 0.20/0.48        | ((sk_B) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.20/0.48        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.20/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.48         ((r2_hidden @ (k2_mcart_1 @ X51) @ X53)
% 0.20/0.48          | ~ (r2_hidden @ X51 @ (k2_zfmisc_1 @ X52 @ X53)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('19', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2)),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))
% 0.20/0.48         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2)))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('21', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.20/0.48       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('23', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['16', '23'])).
% 0.20/0.48  thf('25', plain, (~ (r1_tarski @ sk_B @ (k1_mcart_1 @ sk_A))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['14', '24'])).
% 0.20/0.48  thf(dt_k2_subset_1, axiom,
% 0.20/0.48    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X42 : $i]: (m1_subset_1 @ (k2_subset_1 @ X42) @ (k1_zfmisc_1 @ X42))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.48  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.48  thf('27', plain, (![X41 : $i]: ((k2_subset_1 @ X41) = (X41))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.48  thf('28', plain, (![X42 : $i]: (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X42))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf(t2_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X46 : $i, X47 : $i]:
% 0.20/0.48         ((r2_hidden @ X46 @ X47)
% 0.20/0.48          | (v1_xboole_0 @ X47)
% 0.20/0.48          | ~ (m1_subset_1 @ X46 @ X47))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.48          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf(fc1_subset_1, axiom,
% 0.20/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('31', plain, (![X43 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.48  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf(l33_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X27 : $i, X29 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ (k1_tarski @ X27) @ X29) = (k1_tarski @ X27))
% 0.20/0.48          | (r2_hidden @ X27 @ X29))),
% 0.20/0.48      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.48  thf(t83_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X11 : $i, X13 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.48          | (r2_hidden @ X0 @ X1)
% 0.20/0.48          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.48  thf('37', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.48          | ~ (r2_hidden @ X6 @ X7)
% 0.20/0.48          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.20/0.48          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.48  thf('41', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k1_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X44 : $i, X45 : $i]:
% 0.20/0.48         ((m1_subset_1 @ X44 @ X45) | ~ (r2_hidden @ X44 @ X45))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X48 : $i, X49 : $i]:
% 0.20/0.48         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('45', plain, ((r1_tarski @ sk_B @ (k1_mcart_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain, ($false), inference('demod', [status(thm)], ['25', '45'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
