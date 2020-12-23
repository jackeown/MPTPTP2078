%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eWG5Jvag10

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 198 expanded)
%              Number of leaves         :   37 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  568 (2072 expanded)
%              Number of equality atoms :   40 ( 118 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X33 ) @ X33 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_mcart_1 @ X31 )
        = X30 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_C ) ) @ ( k1_tarski @ sk_A ) ) ),
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
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('25',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ X17 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,
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

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( X20 = k1_xboole_0 )
      | ( X20
       != ( k1_funct_1 @ X19 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ X19 @ X18 )
        = k1_xboole_0 )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
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
      ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','24','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
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
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eWG5Jvag10
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 196 iterations in 0.091s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(t6_mcart_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.55                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.55                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.22/0.55                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.22/0.55                       ( r2_hidden @ G @ B ) ) =>
% 0.22/0.55                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      (![X33 : $i]:
% 0.22/0.55         (((X33) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X33) @ X33))),
% 0.22/0.55      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.22/0.55  thf(t61_funct_2, conjecture,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.22/0.55         ( m1_subset_1 @
% 0.22/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.22/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.55         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.22/0.55            ( m1_subset_1 @
% 0.22/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.22/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.55            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t7_funct_2, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.55       ( ( r2_hidden @ C @ A ) =>
% 0.22/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.55           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X40 @ X41)
% 0.22/0.55          | ((X42) = (k1_xboole_0))
% 0.22/0.55          | ~ (v1_funct_1 @ X43)
% 0.22/0.55          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.22/0.55          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.22/0.55          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ X42))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.22/0.55          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf('4', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.22/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.55  thf('7', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.22/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X33 : $i]:
% 0.22/0.55         (((X33) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X33) @ X33))),
% 0.22/0.55      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ 
% 0.22/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(l3_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X8 @ X9)
% 0.22/0.55          | (r2_hidden @ X8 @ X10)
% 0.22/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      ((((sk_C) = (k1_xboole_0))
% 0.22/0.55        | (r2_hidden @ (sk_B @ sk_C) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['9', '12'])).
% 0.22/0.55  thf(t12_mcart_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.22/0.55       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.55         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.55         (((k1_mcart_1 @ X31) = (X30))
% 0.22/0.55          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ (k1_tarski @ X30) @ X32)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      ((((sk_C) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B @ sk_C)) = (sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      ((((sk_C) = (k1_xboole_0))
% 0.22/0.55        | (r2_hidden @ (sk_B @ sk_C) @ 
% 0.22/0.55           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['9', '12'])).
% 0.22/0.55  thf(t10_mcart_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.55       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.55         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.55         ((r2_hidden @ (k1_mcart_1 @ X27) @ X28)
% 0.22/0.55          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      ((((sk_C) = (k1_xboole_0))
% 0.22/0.55        | (r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_C)) @ (k1_tarski @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.22/0.55        | ((sk_C) = (k1_xboole_0))
% 0.22/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['15', '18'])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.22/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.22/0.56      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      ((((sk_C) = (k1_xboole_0))
% 0.22/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.56  thf('23', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('24', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf(cc1_funct_1, axiom,
% 0.22/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.22/0.56  thf('25', plain, (![X17 : $i]: ((v1_funct_1 @ X17) | ~ (v1_xboole_0 @ X17))),
% 0.22/0.56      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.22/0.56  thf(t60_relat_1, axiom,
% 0.22/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.56  thf('26', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.56  thf(d4_funct_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.56       ( ![B:$i,C:$i]:
% 0.22/0.56         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.22/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.22/0.56               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.56           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.22/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.22/0.56               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.56         ((r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.22/0.56          | ((X20) = (k1_xboole_0))
% 0.22/0.56          | ((X20) != (k1_funct_1 @ X19 @ X18))
% 0.22/0.56          | ~ (v1_funct_1 @ X19)
% 0.22/0.56          | ~ (v1_relat_1 @ X19))),
% 0.22/0.56      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (![X18 : $i, X19 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X19)
% 0.22/0.56          | ~ (v1_funct_1 @ X19)
% 0.22/0.56          | ((k1_funct_1 @ X19 @ X18) = (k1_xboole_0))
% 0.22/0.56          | (r2_hidden @ X18 @ (k1_relat_1 @ X19)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.56          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.56          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['26', '28'])).
% 0.22/0.56  thf(t4_subset_1, axiom,
% 0.22/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.22/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.56  thf(cc1_relset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56       ( v1_relat_1 @ C ) ))).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.56         ((v1_relat_1 @ X24)
% 0.22/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.22/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.56  thf('32', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.56          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['29', '32'])).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.56          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.22/0.56          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['25', '33'])).
% 0.22/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.56  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.22/0.56          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.56  thf(t7_ordinal1, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      (![X22 : $i, X23 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.22/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.56  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.22/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['8', '24', '40'])).
% 0.22/0.56  thf('42', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('43', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.56      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.56  thf('45', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.22/0.56      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.56  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.22/0.56      inference('clc', [status(thm)], ['41', '45'])).
% 0.22/0.56  thf('47', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['0', '46'])).
% 0.22/0.56  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.22/0.56  thf('48', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.22/0.56  thf('49', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.56  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
