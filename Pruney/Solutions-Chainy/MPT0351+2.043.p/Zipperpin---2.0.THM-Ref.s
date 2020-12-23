%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xhBhMdMSFw

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:03 EST 2020

% Result     : Theorem 4.46s
% Output     : Refutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 197 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  677 (2013 expanded)
%              Number of equality atoms :   46 ( 151 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k3_tarski @ ( k2_tarski @ X9 @ X7 ) ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r1_tarski @ X20 @ X18 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_B ) @ X0 )
      | ( X1
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k3_tarski @ ( k2_tarski @ X9 @ X7 ) ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('16',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X9 @ X7 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k3_tarski @ ( k2_tarski @ X9 @ X7 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X9 @ X7 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X9 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k3_tarski @ ( k2_tarski @ X9 @ X7 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X9 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('31',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('32',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('33',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X28 ) @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('35',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k4_subset_1 @ X31 @ X30 @ X32 )
        = ( k2_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k4_subset_1 @ X31 @ X30 @ X32 )
        = ( k3_tarski @ ( k2_tarski @ X30 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X7: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k3_tarski @ ( k2_tarski @ X9 @ X7 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X7 @ X9 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( sk_D @ sk_A @ sk_A @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['29','43'])).

thf('48',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['33','42'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xhBhMdMSFw
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.46/4.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.46/4.65  % Solved by: fo/fo7.sh
% 4.46/4.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.46/4.65  % done 3857 iterations in 4.199s
% 4.46/4.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.46/4.65  % SZS output start Refutation
% 4.46/4.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.46/4.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.46/4.65  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 4.46/4.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.46/4.65  thf(sk_B_type, type, sk_B: $i).
% 4.46/4.65  thf(sk_A_type, type, sk_A: $i).
% 4.46/4.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.46/4.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.46/4.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.46/4.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.46/4.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 4.46/4.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.46/4.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.46/4.65  thf(d3_xboole_0, axiom,
% 4.46/4.65    (![A:$i,B:$i,C:$i]:
% 4.46/4.65     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 4.46/4.65       ( ![D:$i]:
% 4.46/4.65         ( ( r2_hidden @ D @ C ) <=>
% 4.46/4.65           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.46/4.65  thf('0', plain,
% 4.46/4.65      (![X7 : $i, X9 : $i, X11 : $i]:
% 4.46/4.65         (((X11) = (k2_xboole_0 @ X9 @ X7))
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X7)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X9)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 4.46/4.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.46/4.65  thf(l51_zfmisc_1, axiom,
% 4.46/4.65    (![A:$i,B:$i]:
% 4.46/4.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.46/4.65  thf('1', plain,
% 4.46/4.65      (![X22 : $i, X23 : $i]:
% 4.46/4.65         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 4.46/4.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.46/4.65  thf('2', plain,
% 4.46/4.65      (![X7 : $i, X9 : $i, X11 : $i]:
% 4.46/4.65         (((X11) = (k3_tarski @ (k2_tarski @ X9 @ X7)))
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X7)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X9)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 4.46/4.65      inference('demod', [status(thm)], ['0', '1'])).
% 4.46/4.65  thf(t28_subset_1, conjecture,
% 4.46/4.65    (![A:$i,B:$i]:
% 4.46/4.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.46/4.65       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 4.46/4.65  thf(zf_stmt_0, negated_conjecture,
% 4.46/4.65    (~( ![A:$i,B:$i]:
% 4.46/4.65        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.46/4.65          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 4.46/4.65    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 4.46/4.65  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.46/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.65  thf(d2_subset_1, axiom,
% 4.46/4.65    (![A:$i,B:$i]:
% 4.46/4.65     ( ( ( v1_xboole_0 @ A ) =>
% 4.46/4.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 4.46/4.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.46/4.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 4.46/4.65  thf('4', plain,
% 4.46/4.65      (![X24 : $i, X25 : $i]:
% 4.46/4.65         (~ (m1_subset_1 @ X24 @ X25)
% 4.46/4.65          | (r2_hidden @ X24 @ X25)
% 4.46/4.65          | (v1_xboole_0 @ X25))),
% 4.46/4.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.46/4.65  thf('5', plain,
% 4.46/4.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 4.46/4.65        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 4.46/4.65      inference('sup-', [status(thm)], ['3', '4'])).
% 4.46/4.65  thf(fc1_subset_1, axiom,
% 4.46/4.65    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.46/4.65  thf('6', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 4.46/4.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.46/4.65  thf('7', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.46/4.65      inference('clc', [status(thm)], ['5', '6'])).
% 4.46/4.65  thf(d1_zfmisc_1, axiom,
% 4.46/4.65    (![A:$i,B:$i]:
% 4.46/4.65     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 4.46/4.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 4.46/4.65  thf('8', plain,
% 4.46/4.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.46/4.65         (~ (r2_hidden @ X20 @ X19)
% 4.46/4.65          | (r1_tarski @ X20 @ X18)
% 4.46/4.65          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 4.46/4.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.46/4.65  thf('9', plain,
% 4.46/4.65      (![X18 : $i, X20 : $i]:
% 4.46/4.65         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 4.46/4.65      inference('simplify', [status(thm)], ['8'])).
% 4.46/4.65  thf('10', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.46/4.65      inference('sup-', [status(thm)], ['7', '9'])).
% 4.46/4.65  thf(d3_tarski, axiom,
% 4.46/4.65    (![A:$i,B:$i]:
% 4.46/4.65     ( ( r1_tarski @ A @ B ) <=>
% 4.46/4.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.46/4.65  thf('11', plain,
% 4.46/4.65      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.46/4.65         (~ (r2_hidden @ X2 @ X3)
% 4.46/4.65          | (r2_hidden @ X2 @ X4)
% 4.46/4.65          | ~ (r1_tarski @ X3 @ X4))),
% 4.46/4.65      inference('cnf', [status(esa)], [d3_tarski])).
% 4.46/4.65  thf('12', plain,
% 4.46/4.65      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 4.46/4.65      inference('sup-', [status(thm)], ['10', '11'])).
% 4.46/4.65  thf('13', plain,
% 4.46/4.65      (![X0 : $i, X1 : $i]:
% 4.46/4.65         ((r2_hidden @ (sk_D @ X1 @ X0 @ sk_B) @ X1)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_B) @ X0)
% 4.46/4.65          | ((X1) = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 4.46/4.65          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_B) @ sk_A))),
% 4.46/4.65      inference('sup-', [status(thm)], ['2', '12'])).
% 4.46/4.65  thf('14', plain,
% 4.46/4.65      (![X7 : $i, X9 : $i, X11 : $i]:
% 4.46/4.65         (((X11) = (k3_tarski @ (k2_tarski @ X9 @ X7)))
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X7)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X9)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 4.46/4.65      inference('demod', [status(thm)], ['0', '1'])).
% 4.46/4.65  thf('15', plain,
% 4.46/4.65      (![X0 : $i, X1 : $i]:
% 4.46/4.65         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 4.46/4.65          | ((X0) = (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 4.46/4.65      inference('eq_fact', [status(thm)], ['14'])).
% 4.46/4.65  thf('16', plain,
% 4.46/4.65      (![X7 : $i, X9 : $i, X11 : $i]:
% 4.46/4.65         (((X11) = (k2_xboole_0 @ X9 @ X7))
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X7)
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 4.46/4.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.46/4.65  thf('17', plain,
% 4.46/4.65      (![X22 : $i, X23 : $i]:
% 4.46/4.65         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 4.46/4.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.46/4.65  thf('18', plain,
% 4.46/4.65      (![X7 : $i, X9 : $i, X11 : $i]:
% 4.46/4.65         (((X11) = (k3_tarski @ (k2_tarski @ X9 @ X7)))
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X7)
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 4.46/4.65      inference('demod', [status(thm)], ['16', '17'])).
% 4.46/4.65  thf('19', plain,
% 4.46/4.65      (![X0 : $i, X1 : $i]:
% 4.46/4.65         (((X0) = (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 4.46/4.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.46/4.65          | ((X0) = (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 4.46/4.65      inference('sup-', [status(thm)], ['15', '18'])).
% 4.46/4.65  thf('20', plain,
% 4.46/4.65      (![X0 : $i, X1 : $i]:
% 4.46/4.65         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 4.46/4.65          | ((X0) = (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 4.46/4.65      inference('simplify', [status(thm)], ['19'])).
% 4.46/4.65  thf('21', plain,
% 4.46/4.65      (![X0 : $i, X1 : $i]:
% 4.46/4.65         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.46/4.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 4.46/4.65          | ((X0) = (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 4.46/4.65      inference('eq_fact', [status(thm)], ['14'])).
% 4.46/4.65  thf('22', plain,
% 4.46/4.65      (![X0 : $i, X1 : $i]:
% 4.46/4.65         (((X0) = (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 4.46/4.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 4.46/4.65      inference('clc', [status(thm)], ['20', '21'])).
% 4.46/4.65  thf('23', plain,
% 4.46/4.65      (![X7 : $i, X9 : $i, X11 : $i]:
% 4.46/4.65         (((X11) = (k2_xboole_0 @ X9 @ X7))
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X9)
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 4.46/4.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.46/4.65  thf('24', plain,
% 4.46/4.65      (![X22 : $i, X23 : $i]:
% 4.46/4.65         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 4.46/4.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.46/4.65  thf('25', plain,
% 4.46/4.65      (![X7 : $i, X9 : $i, X11 : $i]:
% 4.46/4.65         (((X11) = (k3_tarski @ (k2_tarski @ X9 @ X7)))
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X9)
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 4.46/4.65      inference('demod', [status(thm)], ['23', '24'])).
% 4.46/4.65  thf('26', plain,
% 4.46/4.65      (![X0 : $i, X1 : $i]:
% 4.46/4.65         (((X1) = (k3_tarski @ (k2_tarski @ X0 @ X1)))
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 4.46/4.65          | ((X1) = (k3_tarski @ (k2_tarski @ X0 @ X1))))),
% 4.46/4.65      inference('sup-', [status(thm)], ['22', '25'])).
% 4.46/4.65  thf('27', plain,
% 4.46/4.65      (![X0 : $i, X1 : $i]:
% 4.46/4.65         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 4.46/4.65          | ((X1) = (k3_tarski @ (k2_tarski @ X0 @ X1))))),
% 4.46/4.65      inference('simplify', [status(thm)], ['26'])).
% 4.46/4.65  thf('28', plain,
% 4.46/4.65      ((((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))
% 4.46/4.65        | (r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 4.46/4.65        | (r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 4.46/4.65        | ((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A))))),
% 4.46/4.65      inference('sup-', [status(thm)], ['13', '27'])).
% 4.46/4.65  thf('29', plain,
% 4.46/4.65      (((r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 4.46/4.65        | ((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A))))),
% 4.46/4.65      inference('simplify', [status(thm)], ['28'])).
% 4.46/4.65  thf('30', plain,
% 4.46/4.65      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 4.46/4.65         != (k2_subset_1 @ sk_A))),
% 4.46/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 4.46/4.65  thf('31', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 4.46/4.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 4.46/4.65  thf('32', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 4.46/4.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 4.46/4.65  thf('33', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 4.46/4.65      inference('demod', [status(thm)], ['30', '31', '32'])).
% 4.46/4.65  thf(dt_k2_subset_1, axiom,
% 4.46/4.65    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.46/4.65  thf('34', plain,
% 4.46/4.65      (![X28 : $i]: (m1_subset_1 @ (k2_subset_1 @ X28) @ (k1_zfmisc_1 @ X28))),
% 4.46/4.65      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 4.46/4.65  thf('35', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 4.46/4.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 4.46/4.65  thf('36', plain, (![X28 : $i]: (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X28))),
% 4.46/4.65      inference('demod', [status(thm)], ['34', '35'])).
% 4.46/4.65  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.46/4.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.65  thf(redefinition_k4_subset_1, axiom,
% 4.46/4.65    (![A:$i,B:$i,C:$i]:
% 4.46/4.65     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 4.46/4.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.46/4.65       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 4.46/4.65  thf('38', plain,
% 4.46/4.65      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.46/4.65         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 4.46/4.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 4.46/4.65          | ((k4_subset_1 @ X31 @ X30 @ X32) = (k2_xboole_0 @ X30 @ X32)))),
% 4.46/4.65      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 4.46/4.65  thf('39', plain,
% 4.46/4.65      (![X22 : $i, X23 : $i]:
% 4.46/4.65         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 4.46/4.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.46/4.65  thf('40', plain,
% 4.46/4.65      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.46/4.65         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 4.46/4.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 4.46/4.65          | ((k4_subset_1 @ X31 @ X30 @ X32)
% 4.46/4.65              = (k3_tarski @ (k2_tarski @ X30 @ X32))))),
% 4.46/4.65      inference('demod', [status(thm)], ['38', '39'])).
% 4.46/4.65  thf('41', plain,
% 4.46/4.65      (![X0 : $i]:
% 4.46/4.65         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 4.46/4.65            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 4.46/4.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 4.46/4.65      inference('sup-', [status(thm)], ['37', '40'])).
% 4.46/4.65  thf('42', plain,
% 4.46/4.65      (((k4_subset_1 @ sk_A @ sk_B @ sk_A)
% 4.46/4.65         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 4.46/4.65      inference('sup-', [status(thm)], ['36', '41'])).
% 4.46/4.65  thf('43', plain, (((k3_tarski @ (k2_tarski @ sk_B @ sk_A)) != (sk_A))),
% 4.46/4.65      inference('demod', [status(thm)], ['33', '42'])).
% 4.46/4.65  thf('44', plain, ((r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)),
% 4.46/4.65      inference('simplify_reflect-', [status(thm)], ['29', '43'])).
% 4.46/4.65  thf('45', plain,
% 4.46/4.65      (![X7 : $i, X9 : $i, X11 : $i]:
% 4.46/4.65         (((X11) = (k3_tarski @ (k2_tarski @ X9 @ X7)))
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X7)
% 4.46/4.65          | ~ (r2_hidden @ (sk_D @ X11 @ X7 @ X9) @ X11))),
% 4.46/4.65      inference('demod', [status(thm)], ['16', '17'])).
% 4.46/4.65  thf('46', plain,
% 4.46/4.65      ((~ (r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)
% 4.46/4.65        | ((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A))))),
% 4.46/4.65      inference('sup-', [status(thm)], ['44', '45'])).
% 4.46/4.65  thf('47', plain, ((r2_hidden @ (sk_D @ sk_A @ sk_A @ sk_B) @ sk_A)),
% 4.46/4.65      inference('simplify_reflect-', [status(thm)], ['29', '43'])).
% 4.46/4.65  thf('48', plain, (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 4.46/4.65      inference('demod', [status(thm)], ['46', '47'])).
% 4.46/4.65  thf('49', plain, (((k3_tarski @ (k2_tarski @ sk_B @ sk_A)) != (sk_A))),
% 4.46/4.65      inference('demod', [status(thm)], ['33', '42'])).
% 4.46/4.65  thf('50', plain, ($false),
% 4.46/4.65      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 4.46/4.65  
% 4.46/4.65  % SZS output end Refutation
% 4.46/4.65  
% 4.46/4.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
