%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YWZ2FlxHVd

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 178 expanded)
%              Number of leaves         :   37 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :  517 (1212 expanded)
%              Number of equality atoms :   37 (  87 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( r1_tarski @ X33 @ ( k3_subset_1 @ X34 @ X35 ) )
      | ~ ( r1_tarski @ X35 @ ( k3_subset_1 @ X34 @ X33 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X30: $i] :
      ( ( k1_subset_1 @ X30 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X32: $i] :
      ( ( k2_subset_1 @ X32 )
      = ( k3_subset_1 @ X32 @ ( k1_subset_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('13',plain,(
    ! [X31: $i] :
      ( ( k2_subset_1 @ X31 )
      = X31 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('14',plain,(
    ! [X32: $i] :
      ( X32
      = ( k3_subset_1 @ X32 @ ( k1_subset_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['9','16','19'])).

thf('21',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('35',plain,(
    ! [X22: $i] :
      ( r1_tarski @ X22 @ ( k1_zfmisc_1 @ ( k3_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X25 @ X24 )
      | ~ ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('41',plain,(
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

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('47',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X37 @ ( k3_subset_1 @ X36 @ X37 ) )
      | ( X37
        = ( k1_subset_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('51',plain,(
    ! [X30: $i] :
      ( ( k1_subset_1 @ X30 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('52',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YWZ2FlxHVd
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 404 iterations in 0.109s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(t40_subset_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.20/0.56         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56          ( ( ( r1_tarski @ B @ C ) & 
% 0.20/0.56              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.20/0.56            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.20/0.56  thf('0', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t35_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ![C:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.20/0.56             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.20/0.56          | (r1_tarski @ X33 @ (k3_subset_1 @ X34 @ X35))
% 0.20/0.56          | ~ (r1_tarski @ X35 @ (k3_subset_1 @ X34 @ X33))
% 0.20/0.56          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.20/0.56          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (((r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.56        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.56  thf(t92_xboole_1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('5', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.56  thf('6', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.20/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.20/0.56          | (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ (k5_xboole_0 @ X0 @ X0)))
% 0.20/0.56          | ~ (m1_subset_1 @ (k5_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf('10', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.56  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('11', plain, (![X30 : $i]: ((k1_subset_1 @ X30) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.56  thf(t22_subset_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X32 : $i]:
% 0.20/0.56         ((k2_subset_1 @ X32) = (k3_subset_1 @ X32 @ (k1_subset_1 @ X32)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.56  thf('13', plain, (![X31 : $i]: ((k2_subset_1 @ X31) = (X31))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X32 : $i]: ((X32) = (k3_subset_1 @ X32 @ (k1_subset_1 @ X32)))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf('15', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['11', '14'])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((X1) = (k3_subset_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['10', '15'])).
% 0.20/0.56  thf('17', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.56  thf(t4_subset_1, axiom,
% 0.20/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X38 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (m1_subset_1 @ (k5_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '16', '19'])).
% 0.20/0.56  thf('21', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t1_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.56       ( r1_tarski @ A @ C ) ))).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (r1_tarski @ X5 @ X6)
% 0.20/0.56          | ~ (r1_tarski @ X6 @ X7)
% 0.20/0.56          | (r1_tarski @ X5 @ X7))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.56  thf(t28_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.56  thf('26', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf(t100_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X3 : $i, X4 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.56           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.56  thf('30', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf(t98_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.56           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf(t5_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.56  thf('33', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.56  thf('34', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf(t100_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X22 : $i]: (r1_tarski @ X22 @ (k1_zfmisc_1 @ (k3_tarski @ X22)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.56  thf(t38_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.56       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.56         ((r2_hidden @ X25 @ X24)
% 0.20/0.56          | ~ (r1_tarski @ (k2_tarski @ X23 @ X25) @ X24))),
% 0.20/0.56      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf(l51_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         ((k3_tarski @ (k2_tarski @ X20 @ X21)) = (k2_xboole_0 @ X20 @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.56  thf('40', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('sup+', [status(thm)], ['34', '39'])).
% 0.20/0.56  thf(d2_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (![X27 : $i, X28 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X27 @ X28)
% 0.20/0.56          | (m1_subset_1 @ X27 @ X28)
% 0.20/0.56          | (v1_xboole_0 @ X28))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.56  thf(d1_xboole_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X27 : $i, X28 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.20/0.56      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.56  thf('44', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.56  thf('45', plain, ((r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('47', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf(t38_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.56         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (![X36 : $i, X37 : $i]:
% 0.20/0.56         (~ (r1_tarski @ X37 @ (k3_subset_1 @ X36 @ X37))
% 0.20/0.56          | ((X37) = (k1_subset_1 @ X36))
% 0.20/0.56          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      ((~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.56        | ((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.56  thf('51', plain, (![X30 : $i]: ((k1_subset_1 @ X30) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.56  thf('52', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.56  thf('53', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('54', plain, ($false),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
