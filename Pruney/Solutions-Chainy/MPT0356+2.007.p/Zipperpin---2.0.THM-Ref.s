%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GG2dKInWSX

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:18 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  347 ( 546 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( r2_hidden @ X63 @ X64 )
      | ( r2_hidden @ X63 @ X65 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_A )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(simplify,[status(thm)],['7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k3_subset_1 @ X55 @ X56 )
        = ( k4_xboole_0 @ X55 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ~ ( r1_xboole_0 @ X46 @ X48 )
      | ( r1_tarski @ X46 @ ( k4_xboole_0 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X32 @ X33 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ X43 @ X44 )
      | ( r1_xboole_0 @ X43 @ ( k4_xboole_0 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ~ ( r1_xboole_0 @ X46 @ X48 )
      | ( r1_tarski @ X46 @ ( k4_xboole_0 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k3_subset_1 @ X55 @ X56 )
        = ( k4_xboole_0 @ X55 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GG2dKInWSX
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:50:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.46/1.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.46/1.68  % Solved by: fo/fo7.sh
% 1.46/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.68  % done 4154 iterations in 1.226s
% 1.46/1.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.46/1.68  % SZS output start Refutation
% 1.46/1.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.46/1.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.46/1.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.46/1.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.46/1.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.46/1.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.46/1.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.46/1.68  thf(sk_B_type, type, sk_B: $i).
% 1.46/1.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.46/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.46/1.68  thf(t35_subset_1, conjecture,
% 1.46/1.68    (![A:$i,B:$i]:
% 1.46/1.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.46/1.68       ( ![C:$i]:
% 1.46/1.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.46/1.68           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 1.46/1.68             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.46/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.46/1.68    (~( ![A:$i,B:$i]:
% 1.46/1.68        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.46/1.68          ( ![C:$i]:
% 1.46/1.68            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.46/1.68              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 1.46/1.68                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 1.46/1.68    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 1.46/1.68  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf(d3_tarski, axiom,
% 1.46/1.68    (![A:$i,B:$i]:
% 1.46/1.68     ( ( r1_tarski @ A @ B ) <=>
% 1.46/1.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.46/1.68  thf('1', plain,
% 1.46/1.68      (![X1 : $i, X3 : $i]:
% 1.46/1.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.46/1.68      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.68  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf(l3_subset_1, axiom,
% 1.46/1.68    (![A:$i,B:$i]:
% 1.46/1.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.46/1.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.46/1.68  thf('3', plain,
% 1.46/1.68      (![X63 : $i, X64 : $i, X65 : $i]:
% 1.46/1.68         (~ (r2_hidden @ X63 @ X64)
% 1.46/1.68          | (r2_hidden @ X63 @ X65)
% 1.46/1.68          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X65)))),
% 1.46/1.68      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.46/1.68  thf('4', plain,
% 1.46/1.68      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.46/1.68      inference('sup-', [status(thm)], ['2', '3'])).
% 1.46/1.68  thf('5', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 1.46/1.68      inference('sup-', [status(thm)], ['1', '4'])).
% 1.46/1.68  thf('6', plain,
% 1.46/1.68      (![X1 : $i, X3 : $i]:
% 1.46/1.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.46/1.68      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.68  thf('7', plain,
% 1.46/1.68      (((r1_tarski @ sk_C_1 @ sk_A) | (r1_tarski @ sk_C_1 @ sk_A))),
% 1.46/1.68      inference('sup-', [status(thm)], ['5', '6'])).
% 1.46/1.68  thf('8', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 1.46/1.68      inference('simplify', [status(thm)], ['7'])).
% 1.46/1.68  thf(d10_xboole_0, axiom,
% 1.46/1.68    (![A:$i,B:$i]:
% 1.46/1.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.46/1.68  thf('9', plain,
% 1.46/1.68      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.46/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.46/1.68  thf('10', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.46/1.68      inference('simplify', [status(thm)], ['9'])).
% 1.46/1.68  thf('11', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('12', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf(d5_subset_1, axiom,
% 1.46/1.68    (![A:$i,B:$i]:
% 1.46/1.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.46/1.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.46/1.68  thf('13', plain,
% 1.46/1.68      (![X55 : $i, X56 : $i]:
% 1.46/1.68         (((k3_subset_1 @ X55 @ X56) = (k4_xboole_0 @ X55 @ X56))
% 1.46/1.68          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X55)))),
% 1.46/1.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.46/1.68  thf('14', plain,
% 1.46/1.68      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.46/1.68      inference('sup-', [status(thm)], ['12', '13'])).
% 1.46/1.68  thf(t106_xboole_1, axiom,
% 1.46/1.68    (![A:$i,B:$i,C:$i]:
% 1.46/1.68     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.46/1.68       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.46/1.68  thf('15', plain,
% 1.46/1.68      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.46/1.68         ((r1_xboole_0 @ X7 @ X9)
% 1.46/1.68          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 1.46/1.68      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.46/1.68  thf('16', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 1.46/1.68          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 1.46/1.68      inference('sup-', [status(thm)], ['14', '15'])).
% 1.46/1.68  thf('17', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.46/1.68      inference('sup-', [status(thm)], ['11', '16'])).
% 1.46/1.68  thf(t86_xboole_1, axiom,
% 1.46/1.68    (![A:$i,B:$i,C:$i]:
% 1.46/1.68     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.46/1.68       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 1.46/1.68  thf('18', plain,
% 1.46/1.68      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.46/1.68         (~ (r1_tarski @ X46 @ X47)
% 1.46/1.68          | ~ (r1_xboole_0 @ X46 @ X48)
% 1.46/1.68          | (r1_tarski @ X46 @ (k4_xboole_0 @ X47 @ X48)))),
% 1.46/1.68      inference('cnf', [status(esa)], [t86_xboole_1])).
% 1.46/1.68  thf('19', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))
% 1.46/1.68          | ~ (r1_tarski @ sk_B @ X0))),
% 1.46/1.68      inference('sup-', [status(thm)], ['17', '18'])).
% 1.46/1.68  thf('20', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 1.46/1.68      inference('sup-', [status(thm)], ['10', '19'])).
% 1.46/1.68  thf(t36_xboole_1, axiom,
% 1.46/1.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.46/1.68  thf('21', plain,
% 1.46/1.68      (![X32 : $i, X33 : $i]: (r1_tarski @ (k4_xboole_0 @ X32 @ X33) @ X32)),
% 1.46/1.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.46/1.68  thf('22', plain,
% 1.46/1.68      (![X4 : $i, X6 : $i]:
% 1.46/1.68         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.46/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.46/1.68  thf('23', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]:
% 1.46/1.68         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.46/1.68          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.46/1.68      inference('sup-', [status(thm)], ['21', '22'])).
% 1.46/1.68  thf('24', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 1.46/1.68      inference('sup-', [status(thm)], ['20', '23'])).
% 1.46/1.68  thf('25', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.46/1.68      inference('simplify', [status(thm)], ['9'])).
% 1.46/1.68  thf(t85_xboole_1, axiom,
% 1.46/1.68    (![A:$i,B:$i,C:$i]:
% 1.46/1.68     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.46/1.68  thf('26', plain,
% 1.46/1.68      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.46/1.68         (~ (r1_tarski @ X43 @ X44)
% 1.46/1.68          | (r1_xboole_0 @ X43 @ (k4_xboole_0 @ X45 @ X44)))),
% 1.46/1.68      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.46/1.68  thf('27', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.46/1.68      inference('sup-', [status(thm)], ['25', '26'])).
% 1.46/1.68  thf('28', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.46/1.68      inference('sup+', [status(thm)], ['24', '27'])).
% 1.46/1.68  thf('29', plain,
% 1.46/1.68      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.46/1.68         (~ (r1_tarski @ X46 @ X47)
% 1.46/1.68          | ~ (r1_xboole_0 @ X46 @ X48)
% 1.46/1.68          | (r1_tarski @ X46 @ (k4_xboole_0 @ X47 @ X48)))),
% 1.46/1.68      inference('cnf', [status(esa)], [t86_xboole_1])).
% 1.46/1.68  thf('30', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_B))
% 1.46/1.68          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 1.46/1.68      inference('sup-', [status(thm)], ['28', '29'])).
% 1.46/1.68  thf('31', plain, ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 1.46/1.68      inference('sup-', [status(thm)], ['8', '30'])).
% 1.46/1.68  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('33', plain,
% 1.46/1.68      (![X55 : $i, X56 : $i]:
% 1.46/1.68         (((k3_subset_1 @ X55 @ X56) = (k4_xboole_0 @ X55 @ X56))
% 1.46/1.68          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X55)))),
% 1.46/1.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.46/1.68  thf('34', plain,
% 1.46/1.68      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.46/1.68      inference('sup-', [status(thm)], ['32', '33'])).
% 1.46/1.68  thf('35', plain, ((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 1.46/1.68      inference('demod', [status(thm)], ['31', '34'])).
% 1.46/1.68  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 1.46/1.68  
% 1.46/1.68  % SZS output end Refutation
% 1.46/1.68  
% 1.53/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
