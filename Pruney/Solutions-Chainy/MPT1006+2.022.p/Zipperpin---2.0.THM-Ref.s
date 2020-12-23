%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A4KyfDuloB

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:09 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 151 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  474 ( 947 expanded)
%              Number of equality atoms :   26 (  64 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('3',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('15',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['7','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( m1_subset_1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X19 @ X20 @ X21 @ X22 ) @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) )
      | ( r1_tarski @ ( k8_relset_1 @ X1 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X1 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X2 ) @ X1 )
      | ~ ( v1_funct_1 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
      | ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ X0 @ ( sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('41',plain,(
    v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,
    ( ( sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('44',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('48',plain,
    ( ( sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ X1 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','43','46','47','48'])).

thf('50',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_xboole_0 @ ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['21','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A4KyfDuloB
% 0.16/0.37  % Computer   : n016.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:56:49 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 872 iterations in 0.405s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.69/0.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.69/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.69/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.89  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.69/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.89  thf(l13_xboole_0, axiom,
% 0.69/0.89    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.89  thf('0', plain,
% 0.69/0.89      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('1', plain,
% 0.69/0.89      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('2', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('sup+', [status(thm)], ['0', '1'])).
% 0.69/0.89  thf(t60_funct_2, conjecture,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.69/0.89         ( m1_subset_1 @
% 0.69/0.89           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.69/0.89       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.89        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.69/0.89            ( m1_subset_1 @
% 0.69/0.89              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.69/0.89          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.69/0.89  thf('3', plain,
% 0.69/0.89      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1) != (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('4', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((X0) != (k1_xboole_0))
% 0.69/0.89          | ~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1))
% 0.69/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.89  thf('5', plain,
% 0.69/0.89      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.89        | ~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1)))),
% 0.69/0.89      inference('simplify', [status(thm)], ['4'])).
% 0.69/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.89  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('7', plain,
% 0.69/0.89      (~ (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1))),
% 0.69/0.89      inference('simplify_reflect+', [status(thm)], ['5', '6'])).
% 0.69/0.89  thf('8', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(t113_zfmisc_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.89       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.69/0.89  thf('9', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['9'])).
% 0.69/0.89  thf('11', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.69/0.89      inference('demod', [status(thm)], ['8', '10'])).
% 0.69/0.89  thf('12', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['12'])).
% 0.69/0.89  thf(cc4_relset_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( v1_xboole_0 @ A ) =>
% 0.69/0.89       ( ![C:$i]:
% 0.69/0.89         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.69/0.89           ( v1_xboole_0 @ C ) ) ) ))).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.69/0.89         (~ (v1_xboole_0 @ X16)
% 0.69/0.89          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 0.69/0.89          | (v1_xboole_0 @ X17))),
% 0.69/0.89      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.69/0.89  thf('15', plain,
% 0.69/0.89      (![X1 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.69/0.89          | (v1_xboole_0 @ X1)
% 0.69/0.89          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.69/0.89  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.89  thf('17', plain,
% 0.69/0.89      (![X1 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.69/0.89          | (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('demod', [status(thm)], ['15', '16'])).
% 0.69/0.89  thf('18', plain, ((v1_xboole_0 @ sk_C)),
% 0.69/0.89      inference('sup-', [status(thm)], ['11', '17'])).
% 0.69/0.89  thf('19', plain,
% 0.69/0.89      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('20', plain, (((sk_C) = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      (~ (v1_xboole_0 @ 
% 0.69/0.89          (k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.69/0.89      inference('demod', [status(thm)], ['7', '20'])).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['9'])).
% 0.69/0.89  thf(d1_xboole_0, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.69/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.89  thf(d2_subset_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( v1_xboole_0 @ A ) =>
% 0.69/0.89         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.69/0.89       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.89         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.89  thf('24', plain,
% 0.69/0.89      (![X7 : $i, X8 : $i]:
% 0.69/0.89         (~ (r2_hidden @ X7 @ X8)
% 0.69/0.89          | (m1_subset_1 @ X7 @ X8)
% 0.69/0.89          | (v1_xboole_0 @ X8))),
% 0.69/0.89      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.69/0.89  thf('25', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.89  thf('26', plain,
% 0.69/0.89      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.69/0.89      inference('clc', [status(thm)], ['24', '25'])).
% 0.69/0.89  thf('27', plain,
% 0.69/0.89      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['23', '26'])).
% 0.69/0.89  thf(t47_funct_2, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89     ( ( ( v1_funct_1 @ D ) & 
% 0.69/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.89       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.69/0.89  thf('28', plain,
% 0.69/0.89      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.69/0.89         ((r1_tarski @ (k8_relset_1 @ X19 @ X20 @ X21 @ X22) @ X19)
% 0.69/0.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.69/0.89          | ~ (v1_funct_1 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.69/0.89          | ~ (v1_funct_1 @ (sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))
% 0.69/0.89          | (r1_tarski @ 
% 0.69/0.89             (k8_relset_1 @ X1 @ X0 @ 
% 0.69/0.89              (sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X2) @ 
% 0.69/0.89             X1))),
% 0.69/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.89  thf(fc1_subset_1, axiom,
% 0.69/0.89    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.89  thf('30', plain, (![X10 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.89  thf('31', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         ((r1_tarski @ 
% 0.69/0.89           (k8_relset_1 @ X1 @ X0 @ 
% 0.69/0.89            (sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X2) @ 
% 0.69/0.89           X1)
% 0.69/0.89          | ~ (v1_funct_1 @ (sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))))),
% 0.69/0.89      inference('clc', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('32', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_funct_1 @ (sk_B @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.69/0.89          | (r1_tarski @ 
% 0.69/0.89             (k8_relset_1 @ k1_xboole_0 @ X0 @ 
% 0.69/0.89              (sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))) @ X1) @ 
% 0.69/0.89             k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['22', '31'])).
% 0.69/0.89  thf('33', plain,
% 0.69/0.89      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['23', '26'])).
% 0.69/0.89  thf(t3_subset, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.89  thf('34', plain,
% 0.69/0.89      (![X11 : $i, X12 : $i]:
% 0.69/0.89         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.69/0.89          | (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.89  thf('36', plain, (![X10 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      (![X0 : $i]: (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.69/0.89      inference('clc', [status(thm)], ['35', '36'])).
% 0.69/0.89  thf('38', plain,
% 0.69/0.89      (![X11 : $i, X13 : $i]:
% 0.69/0.89         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.69/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.89  thf('39', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (m1_subset_1 @ (sk_B @ (k1_zfmisc_1 @ X0)) @ (k1_zfmisc_1 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.89  thf('40', plain,
% 0.69/0.89      (![X1 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.69/0.89          | (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('demod', [status(thm)], ['15', '16'])).
% 0.69/0.89  thf('41', plain, ((v1_xboole_0 @ (sk_B @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.89  thf('42', plain,
% 0.69/0.89      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.69/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.89  thf('43', plain, (((sk_B @ (k1_zfmisc_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['41', '42'])).
% 0.69/0.89  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.69/0.89  thf('44', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.89      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.69/0.89  thf(fc3_funct_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.69/0.89       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.69/0.89  thf('45', plain, (![X15 : $i]: (v1_funct_1 @ (k6_relat_1 @ X15))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.89  thf('46', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.69/0.89      inference('sup+', [status(thm)], ['44', '45'])).
% 0.69/0.89  thf('47', plain,
% 0.69/0.89      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['9'])).
% 0.69/0.89  thf('48', plain, (((sk_B @ (k1_zfmisc_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['41', '42'])).
% 0.69/0.89  thf('49', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.69/0.89          k1_xboole_0)),
% 0.69/0.89      inference('demod', [status(thm)], ['32', '43', '46', '47', '48'])).
% 0.69/0.89  thf('50', plain,
% 0.69/0.89      (![X11 : $i, X13 : $i]:
% 0.69/0.89         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.69/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.89  thf('51', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (m1_subset_1 @ (k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0) @ 
% 0.69/0.89          (k1_zfmisc_1 @ k1_xboole_0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      (![X1 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.69/0.89          | (v1_xboole_0 @ X1))),
% 0.69/0.89      inference('demod', [status(thm)], ['15', '16'])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (v1_xboole_0 @ (k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0))),
% 0.69/0.89      inference('sup-', [status(thm)], ['51', '52'])).
% 0.69/0.89  thf('54', plain, ($false), inference('demod', [status(thm)], ['21', '53'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
