%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1pOcA4Kr3a

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:24 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 205 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  559 (2663 expanded)
%              Number of equality atoms :   37 ( 149 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X19 = k1_xboole_0 )
      | ( X19
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X20 ) @ X18 )
      | ( X20
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( k1_funct_1 @ X18 @ X17 ) ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','19'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('21',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X27 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 = X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

thf('39',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('41',plain,
    ( ( sk_B @ ( k1_tarski @ sk_A ) )
    = sk_A ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('43',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['34','41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['20','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1pOcA4Kr3a
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 78 iterations in 0.054s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.55  thf(t61_funct_2, conjecture,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.55         ( m1_subset_1 @
% 0.35/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.55         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.55            ( m1_subset_1 @
% 0.35/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.55            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.35/0.55  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(d4_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ![B:$i,C:$i]:
% 0.35/0.55         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.55             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.55               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.55           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.35/0.55             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.55               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.35/0.55         ((r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.35/0.55          | ((X19) = (k1_xboole_0))
% 0.35/0.55          | ((X19) != (k1_funct_1 @ X18 @ X17))
% 0.35/0.55          | ~ (v1_funct_1 @ X18)
% 0.35/0.55          | ~ (v1_relat_1 @ X18))),
% 0.35/0.55      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (![X17 : $i, X18 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X18)
% 0.35/0.55          | ~ (v1_funct_1 @ X18)
% 0.35/0.55          | ((k1_funct_1 @ X18 @ X17) = (k1_xboole_0))
% 0.35/0.55          | (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['1'])).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.35/0.55          | (r2_hidden @ (k4_tarski @ X17 @ X20) @ X18)
% 0.35/0.55          | ((X20) != (k1_funct_1 @ X18 @ X17))
% 0.35/0.55          | ~ (v1_funct_1 @ X18)
% 0.35/0.55          | ~ (v1_relat_1 @ X18))),
% 0.35/0.55      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (![X17 : $i, X18 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X18)
% 0.35/0.55          | ~ (v1_funct_1 @ X18)
% 0.35/0.55          | (r2_hidden @ (k4_tarski @ X17 @ (k1_funct_1 @ X18 @ X17)) @ X18)
% 0.35/0.55          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.35/0.55          | ~ (v1_funct_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.35/0.55          | ~ (v1_funct_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['2', '4'])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_funct_1 @ X0)
% 0.35/0.55          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ 
% 0.35/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(l3_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X14 @ X15)
% 0.35/0.55          | (r2_hidden @ X14 @ X16)
% 0.35/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.35/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.35/0.55          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.35/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.35/0.55          | ~ (v1_relat_1 @ sk_C)
% 0.35/0.55          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.35/0.55             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.35/0.55  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ 
% 0.35/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(cc1_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( v1_relat_1 @ C ) ))).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.55         ((v1_relat_1 @ X21)
% 0.35/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.55  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.35/0.55          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.35/0.55             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.35/0.55      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.35/0.55  thf(t128_zfmisc_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.55     ( ( r2_hidden @
% 0.35/0.55         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.35/0.55       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.55         ((r2_hidden @ X9 @ X10)
% 0.35/0.55          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ 
% 0.35/0.55               (k2_zfmisc_1 @ (k1_tarski @ X7) @ X10)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.55  thf('18', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('19', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.55  thf('20', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.35/0.55      inference('demod', [status(thm)], ['0', '19'])).
% 0.35/0.55  thf(t9_mcart_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ~( ( r2_hidden @ B @ A ) & 
% 0.35/0.55                 ( ![C:$i,D:$i]:
% 0.35/0.55                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.35/0.55                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (![X24 : $i]:
% 0.35/0.55         (((X24) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X24) @ X24))),
% 0.35/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ 
% 0.35/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t7_funct_2, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.55       ( ( r2_hidden @ C @ A ) =>
% 0.35/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.55           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X27 @ X28)
% 0.35/0.55          | ((X29) = (k1_xboole_0))
% 0.35/0.55          | ~ (v1_funct_1 @ X30)
% 0.35/0.55          | ~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.35/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ X30 @ X27) @ X29))),
% 0.35/0.55      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.35/0.55          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.35/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.35/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.55  thf('25', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.35/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.35/0.55  thf('28', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.35/0.55        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.35/0.55           sk_B_1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['21', '29'])).
% 0.35/0.55  thf(t1_boole, axiom,
% 0.35/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.55  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.55  thf(t49_zfmisc_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (![X12 : $i, X13 : $i]:
% 0.35/0.55         ((k2_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.35/0.55  thf('33', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ sk_B_1)),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.35/0.55          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.35/0.55             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.35/0.55      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.55         (((X8) = (X7))
% 0.35/0.55          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ 
% 0.35/0.55               (k2_zfmisc_1 @ (k1_tarski @ X7) @ X10)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0)) | ((X0) = (sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ sk_B_1)),
% 0.35/0.55      inference('simplify_reflect-', [status(thm)], ['30', '33'])).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      (((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.35/0.55        | ((sk_B @ (k1_tarski @ sk_A)) = (sk_A)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.35/0.55  thf('40', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.35/0.55      inference('demod', [status(thm)], ['0', '19'])).
% 0.35/0.55  thf('41', plain, (((sk_B @ (k1_tarski @ sk_A)) = (sk_A))),
% 0.35/0.55      inference('clc', [status(thm)], ['39', '40'])).
% 0.35/0.55  thf('42', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.55  thf('43', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.35/0.55      inference('demod', [status(thm)], ['34', '41', '42'])).
% 0.35/0.55  thf('44', plain, ($false), inference('demod', [status(thm)], ['20', '43'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
