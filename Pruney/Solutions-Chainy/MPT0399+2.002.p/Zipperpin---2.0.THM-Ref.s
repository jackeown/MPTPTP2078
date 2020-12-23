%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3vgzFFg3f4

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 131 expanded)
%              Number of leaves         :   41 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  529 ( 745 expanded)
%              Number of equality atoms :   42 (  73 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('1',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X56 ) @ ( k3_tarski @ X57 ) )
      | ~ ( r1_setfam_1 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('4',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('10',plain,(
    ! [X37: $i] :
      ( r1_tarski @ X37 @ ( k1_zfmisc_1 @ ( k3_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('11',plain,(
    r1_tarski @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35
        = ( k1_tarski @ X34 ) )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A
      = ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_A
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(fc7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) )).

thf('28',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc7_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ~ ( v1_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( v1_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,
    ( sk_A
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X41: $i] :
      ( ( k1_subset_1 @ X41 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X42 ) @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup+',[status(thm)],['37','40'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('42',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ X39 )
      | ( r2_hidden @ X38 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('45',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( r2_hidden @ ( sk_D @ X51 @ X52 ) @ X52 )
      | ~ ( r2_hidden @ X51 @ X53 )
      | ~ ( r1_setfam_1 @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['36','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3vgzFFg3f4
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 184 iterations in 0.064s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.54                                           $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(t1_zfmisc_1, axiom,
% 0.21/0.54    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.21/0.54  thf('0', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.54  thf(t21_setfam_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.21/0.54  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t18_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_setfam_1 @ A @ B ) =>
% 0.21/0.54       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X56 : $i, X57 : $i]:
% 0.21/0.54         ((r1_tarski @ (k3_tarski @ X56) @ (k3_tarski @ X57))
% 0.21/0.54          | ~ (r1_setfam_1 @ X56 @ X57))),
% 0.21/0.54      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.54  thf('4', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.54  thf('5', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.54  thf('6', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i]:
% 0.21/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain, (((k3_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.54  thf(t100_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X37 : $i]: (r1_tarski @ X37 @ (k1_zfmisc_1 @ (k3_tarski @ X37)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.21/0.54  thf('11', plain, ((r1_tarski @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.54  thf(l3_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X34 : $i, X35 : $i]:
% 0.21/0.54         (((X35) = (k1_tarski @ X34))
% 0.21/0.54          | ((X35) = (k1_xboole_0))
% 0.21/0.54          | ~ (r1_tarski @ X35 @ (k1_tarski @ X34)))),
% 0.21/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.54          | ((X0) = (k1_xboole_0))
% 0.21/0.54          | ((X0) = (k1_tarski @ k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.54          | ((X0) = (k1_xboole_0))
% 0.21/0.54          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((((sk_A) = (k1_zfmisc_1 @ k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.54  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain, (((sk_A) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain, (((sk_A) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '19'])).
% 0.21/0.54  thf(t69_enumset1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.54  thf('21', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.54  thf(t70_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.54  thf(t71_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.54  thf(t72_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.54         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.54           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.54  thf(t73_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.54     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.54       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.21/0.54           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.54  thf(t74_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.54     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.54       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.54         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.21/0.54           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 0.21/0.54      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.54  thf(t75_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.54     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.54       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.54         ((k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.21/0.54           = (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.21/0.54      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.21/0.54  thf(fc7_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.54     ( ~( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, 
% 0.21/0.54         X50 : $i]:
% 0.21/0.54         ~ (v1_xboole_0 @ 
% 0.21/0.54            (k6_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc7_subset_1])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         ~ (v1_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.54         ~ (v1_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         ~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '33'])).
% 0.21/0.54  thf('35', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '34'])).
% 0.21/0.54  thf('36', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '35'])).
% 0.21/0.54  thf('37', plain, (((sk_A) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('38', plain, (![X41 : $i]: ((k1_subset_1 @ X41) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.54  thf(dt_k1_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X42 : $i]: (m1_subset_1 @ (k1_subset_1 @ X42) @ (k1_zfmisc_1 @ X42))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('sup+', [status(thm)], ['37', '40'])).
% 0.21/0.54  thf(d2_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X38 : $i, X39 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X38 @ X39)
% 0.21/0.54          | (r2_hidden @ X38 @ X39)
% 0.21/0.54          | (v1_xboole_0 @ X39))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.54  thf('43', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ k1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf('44', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d2_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.54              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_D @ X51 @ X52) @ X52)
% 0.21/0.54          | ~ (r2_hidden @ X51 @ X53)
% 0.21/0.54          | ~ (r1_setfam_1 @ X53 @ X52))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((v1_xboole_0 @ sk_A)
% 0.21/0.54        | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '46'])).
% 0.21/0.54  thf(t7_boole, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_boole])).
% 0.21/0.54  thf('49', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.54  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('51', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain, ($false), inference('demod', [status(thm)], ['36', '51'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
