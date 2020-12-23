%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTzqcBuiJ2

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:06 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 479 expanded)
%              Number of leaves         :   27 ( 159 expanded)
%              Depth                    :   12
%              Number of atoms          :  492 (3346 expanded)
%              Number of equality atoms :   59 ( 323 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X46 ) @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X52 ) )
      | ( ( k4_subset_1 @ X52 @ X51 @ X53 )
        = ( k2_xboole_0 @ X51 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ( r1_tarski @ X36 @ X34 )
      | ( X35
       != ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ X36 @ X34 )
      | ~ ( r2_hidden @ X36 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('16',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X42 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('21',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('24',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A != sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    v1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['25'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( X2 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('32',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('33',plain,
    ( ( k4_subset_1 @ o_0_0_xboole_0 @ sk_B_1 @ o_0_0_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['6','30','31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X42 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('40',plain,
    ( ( sk_A != sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( X2 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('43',plain,(
    sk_B_1 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X45 ) @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X43: $i] :
      ( ( k1_subset_1 @ X43 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('46',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('47',plain,(
    ! [X43: $i] :
      ( ( k1_subset_1 @ X43 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k4_subset_1 @ X58 @ X59 @ ( k3_subset_1 @ X58 @ X59 ) )
        = ( k2_subset_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('50',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('51',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k4_subset_1 @ X58 @ X59 @ ( k3_subset_1 @ X58 @ X59 ) )
        = X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ o_0_0_xboole_0 @ ( k3_subset_1 @ X0 @ o_0_0_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X57: $i] :
      ( ( k2_subset_1 @ X57 )
      = ( k3_subset_1 @ X57 @ ( k1_subset_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('54',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('55',plain,(
    ! [X43: $i] :
      ( ( k1_subset_1 @ X43 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('56',plain,(
    ! [X57: $i] :
      ( X57
      = ( k3_subset_1 @ X57 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ o_0_0_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['52','56'])).

thf('58',plain,(
    sk_B_1 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('59',plain,
    ( o_0_0_xboole_0
    = ( k2_xboole_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['33','43','57','58'])).

thf('60',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('61',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('62',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('63',plain,(
    ( k2_xboole_0 @ sk_B_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    sk_B_1 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('65',plain,(
    ( k2_xboole_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTzqcBuiJ2
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 16:34:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 198 iterations in 0.062s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.23/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.23/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.54  thf(dt_k2_subset_1, axiom,
% 0.23/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.54  thf('0', plain,
% 0.23/0.54      (![X46 : $i]: (m1_subset_1 @ (k2_subset_1 @ X46) @ (k1_zfmisc_1 @ X46))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.23/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.54  thf('1', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.54  thf('2', plain, (![X46 : $i]: (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X46))),
% 0.23/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.54  thf(t28_subset_1, conjecture,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i,B:$i]:
% 0.23/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.23/0.54  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.23/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.23/0.54  thf('4', plain,
% 0.23/0.54      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52))
% 0.23/0.54          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X52))
% 0.23/0.54          | ((k4_subset_1 @ X52 @ X51 @ X53) = (k2_xboole_0 @ X51 @ X53)))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.23/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.54  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d2_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X40 : $i, X41 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X40 @ X41)
% 0.23/0.54          | (r2_hidden @ X40 @ X41)
% 0.23/0.54          | (v1_xboole_0 @ X41))),
% 0.23/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.54        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf(d1_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.23/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X36 @ X35)
% 0.23/0.54          | (r1_tarski @ X36 @ X34)
% 0.23/0.54          | ((X35) != (k1_zfmisc_1 @ X34)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (![X34 : $i, X36 : $i]:
% 0.23/0.54         ((r1_tarski @ X36 @ X34) | ~ (r2_hidden @ X36 @ (k1_zfmisc_1 @ X34)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['9', '11'])).
% 0.23/0.54  thf(t12_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i]:
% 0.23/0.54         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.23/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.54        | ((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.54  thf('15', plain, (![X46 : $i]: (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X46))),
% 0.23/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X41 : $i, X42 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X42 @ X41)
% 0.23/0.54          | (v1_xboole_0 @ X42)
% 0.23/0.54          | ~ (v1_xboole_0 @ X41))),
% 0.23/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (![X0 : $i]: (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (v1_xboole_0 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      ((((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)) | (v1_xboole_0 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['14', '17'])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k2_subset_1 @ sk_A))
% 0.23/0.54         != (k2_subset_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('20', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.54  thf('21', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.54  thf('22', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) != (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.54  thf('24', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('25', plain, ((((sk_A) != (sk_A)) | (v1_xboole_0 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['18', '24'])).
% 0.23/0.54  thf('26', plain, ((v1_xboole_0 @ sk_A)),
% 0.23/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.54  thf(l13_xboole_0, axiom,
% 0.23/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.23/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.23/0.54  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.23/0.54  thf('28', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (![X2 : $i]: (((X2) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.23/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.54  thf('30', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.54  thf('31', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.54  thf('32', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      (((k4_subset_1 @ o_0_0_xboole_0 @ sk_B_1 @ o_0_0_xboole_0)
% 0.23/0.54         = (k2_xboole_0 @ sk_B_1 @ o_0_0_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['6', '30', '31', '32'])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.54        | ((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.54  thf('35', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('36', plain,
% 0.23/0.54      (![X41 : $i, X42 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X42 @ X41)
% 0.23/0.54          | (v1_xboole_0 @ X42)
% 0.23/0.54          | ~ (v1_xboole_0 @ X41))),
% 0.23/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.54  thf('37', plain,
% 0.23/0.54      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.23/0.54  thf('38', plain,
% 0.23/0.54      ((((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['34', '37'])).
% 0.23/0.54  thf('39', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('40', plain, ((((sk_A) != (sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.23/0.54  thf('41', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.23/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.23/0.54  thf('42', plain,
% 0.23/0.54      (![X2 : $i]: (((X2) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.23/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.54  thf('43', plain, (((sk_B_1) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.54  thf(dt_k1_subset_1, axiom,
% 0.23/0.54    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.54  thf('44', plain,
% 0.23/0.54      (![X45 : $i]: (m1_subset_1 @ (k1_subset_1 @ X45) @ (k1_zfmisc_1 @ X45))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.23/0.54  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.54  thf('45', plain, (![X43 : $i]: ((k1_subset_1 @ X43) = (k1_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.23/0.54  thf('46', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.54  thf('47', plain, (![X43 : $i]: ((k1_subset_1 @ X43) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.23/0.54  thf('48', plain,
% 0.23/0.54      (![X45 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X45))),
% 0.23/0.54      inference('demod', [status(thm)], ['44', '47'])).
% 0.23/0.54  thf(t25_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.23/0.54         ( k2_subset_1 @ A ) ) ))).
% 0.23/0.54  thf('49', plain,
% 0.23/0.54      (![X58 : $i, X59 : $i]:
% 0.23/0.54         (((k4_subset_1 @ X58 @ X59 @ (k3_subset_1 @ X58 @ X59))
% 0.23/0.54            = (k2_subset_1 @ X58))
% 0.23/0.54          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X58)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.23/0.54  thf('50', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.54  thf('51', plain,
% 0.23/0.54      (![X58 : $i, X59 : $i]:
% 0.23/0.54         (((k4_subset_1 @ X58 @ X59 @ (k3_subset_1 @ X58 @ X59)) = (X58))
% 0.23/0.54          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X58)))),
% 0.23/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.23/0.54  thf('52', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((k4_subset_1 @ X0 @ o_0_0_xboole_0 @ 
% 0.23/0.54           (k3_subset_1 @ X0 @ o_0_0_xboole_0)) = (X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['48', '51'])).
% 0.23/0.54  thf(t22_subset_1, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.23/0.54  thf('53', plain,
% 0.23/0.54      (![X57 : $i]:
% 0.23/0.54         ((k2_subset_1 @ X57) = (k3_subset_1 @ X57 @ (k1_subset_1 @ X57)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.23/0.54  thf('54', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.54  thf('55', plain, (![X43 : $i]: ((k1_subset_1 @ X43) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.23/0.54  thf('56', plain,
% 0.23/0.54      (![X57 : $i]: ((X57) = (k3_subset_1 @ X57 @ o_0_0_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.23/0.54  thf('57', plain,
% 0.23/0.54      (![X0 : $i]: ((k4_subset_1 @ X0 @ o_0_0_xboole_0 @ X0) = (X0))),
% 0.23/0.54      inference('demod', [status(thm)], ['52', '56'])).
% 0.23/0.54  thf('58', plain, (((sk_B_1) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.54  thf('59', plain,
% 0.23/0.54      (((o_0_0_xboole_0) = (k2_xboole_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['33', '43', '57', '58'])).
% 0.23/0.54  thf('60', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.54  thf('61', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.54  thf('62', plain, (((sk_A) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.54  thf('63', plain,
% 0.23/0.54      (((k2_xboole_0 @ sk_B_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.23/0.54  thf('64', plain, (((sk_B_1) = (o_0_0_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.54  thf('65', plain,
% 0.23/0.54      (((k2_xboole_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['63', '64'])).
% 0.23/0.54  thf('66', plain, ($false),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['59', '65'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
