%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y5FjkqA3Xt

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:15 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 198 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  564 (2068 expanded)
%              Number of equality atoms :   41 ( 120 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('0',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X34 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_mcart_1 @ X26 )
        = X25 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ ( k1_tarski @ X25 ) @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ sk_C ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('26',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('27',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( X18 = k1_xboole_0 )
      | ( X18
       != ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k1_funct_1 @ X17 @ X16 )
        = k1_xboole_0 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','24','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('45',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','46'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('48',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y5FjkqA3Xt
% 0.17/0.37  % Computer   : n001.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 21:01:45 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 174 iterations in 0.101s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.40/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.40/0.58  thf(t6_mcart_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ~( ( r2_hidden @ B @ A ) & 
% 0.40/0.58                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.40/0.58                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.40/0.58                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.40/0.58                       ( r2_hidden @ G @ B ) ) =>
% 0.40/0.58                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (![X28 : $i]:
% 0.40/0.58         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X28) @ X28))),
% 0.40/0.58      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.40/0.58  thf(t61_funct_2, conjecture,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.40/0.58         ( m1_subset_1 @
% 0.40/0.58           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.40/0.58       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.40/0.58         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.40/0.58            ( m1_subset_1 @
% 0.40/0.58              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.40/0.58          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.40/0.58            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t7_funct_2, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58       ( ( r2_hidden @ C @ A ) =>
% 0.40/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.40/0.58           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X34 @ X35)
% 0.40/0.58          | ((X36) = (k1_xboole_0))
% 0.40/0.58          | ~ (v1_funct_1 @ X37)
% 0.40/0.58          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.40/0.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.40/0.58          | (r2_hidden @ (k1_funct_1 @ X37 @ X34) @ X36))),
% 0.40/0.58      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.40/0.58          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.40/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.40/0.58          | ((sk_B_2) = (k1_xboole_0))
% 0.40/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf('4', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.40/0.58          | ((sk_B_2) = (k1_xboole_0))
% 0.40/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.40/0.58  thf('7', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.40/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X28 : $i]:
% 0.40/0.58         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X28) @ X28))),
% 0.40/0.58      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_C @ 
% 0.40/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(l3_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X9 @ X10)
% 0.40/0.58          | (r2_hidden @ X9 @ X11)
% 0.40/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.40/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.40/0.58          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      ((((sk_C) = (k1_xboole_0))
% 0.40/0.58        | (r2_hidden @ (sk_B_1 @ sk_C) @ 
% 0.40/0.58           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '12'])).
% 0.40/0.58  thf(t12_mcart_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.40/0.58       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.40/0.58         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.58         (((k1_mcart_1 @ X26) = (X25))
% 0.40/0.58          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ (k1_tarski @ X25) @ X27)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      ((((sk_C) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B_1 @ sk_C)) = (sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      ((((sk_C) = (k1_xboole_0))
% 0.40/0.58        | (r2_hidden @ (sk_B_1 @ sk_C) @ 
% 0.40/0.58           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '12'])).
% 0.40/0.58  thf(t10_mcart_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.40/0.58       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.40/0.58         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.58         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 0.40/0.58          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      ((((sk_C) = (k1_xboole_0))
% 0.40/0.58        | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ sk_C)) @ (k1_tarski @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.40/0.58        | ((sk_C) = (k1_xboole_0))
% 0.40/0.58        | ((sk_C) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['15', '18'])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.40/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      ((((sk_C) = (k1_xboole_0))
% 0.40/0.58        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.58  thf('23', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('24', plain, (((sk_C) = (k1_xboole_0))),
% 0.40/0.58      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf(cc1_relat_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.40/0.58  thf('25', plain, (![X14 : $i]: ((v1_relat_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.58  thf(cc1_funct_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.40/0.58  thf('26', plain, (![X15 : $i]: ((v1_funct_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.40/0.58  thf(t60_relat_1, axiom,
% 0.40/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('27', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.58  thf(d4_funct_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.58       ( ![B:$i,C:$i]:
% 0.40/0.58         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.40/0.58             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.40/0.58               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.58           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.40/0.58             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.40/0.58               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.58         ((r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.40/0.58          | ((X18) = (k1_xboole_0))
% 0.40/0.58          | ((X18) != (k1_funct_1 @ X17 @ X16))
% 0.40/0.58          | ~ (v1_funct_1 @ X17)
% 0.40/0.58          | ~ (v1_relat_1 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X17)
% 0.40/0.58          | ~ (v1_funct_1 @ X17)
% 0.40/0.58          | ((k1_funct_1 @ X17 @ X16) = (k1_xboole_0))
% 0.40/0.58          | (r2_hidden @ X16 @ (k1_relat_1 @ X17)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['28'])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.40/0.58          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.40/0.58          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.40/0.58          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['27', '29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.58          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.40/0.58          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '30'])).
% 0.40/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.58  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.58          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.40/0.58          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.58          | (r2_hidden @ X0 @ k1_xboole_0)
% 0.40/0.58          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '33'])).
% 0.40/0.58  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.40/0.58          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf(t7_ordinal1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X20 : $i, X21 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.40/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.40/0.58          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.58  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.40/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '24', '40'])).
% 0.40/0.58  thf('42', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('43', plain, (((sk_C) = (k1_xboole_0))),
% 0.40/0.58      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.58  thf('45', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.40/0.58      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.40/0.58  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.40/0.58      inference('clc', [status(thm)], ['41', '45'])).
% 0.40/0.58  thf('47', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '46'])).
% 0.40/0.58  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.40/0.58  thf('48', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.40/0.58  thf('49', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.58  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
