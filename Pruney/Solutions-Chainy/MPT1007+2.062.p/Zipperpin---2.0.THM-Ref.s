%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6EBmWp9gnh

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:24 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 139 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  540 (1676 expanded)
%              Number of equality atoms :   26 (  80 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( X21 = k1_xboole_0 )
      | ( X21
       != ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_funct_1 @ X20 @ X19 )
        = k1_xboole_0 )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X22 ) @ X20 )
      | ( X22
       != ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( k1_funct_1 @ X20 @ X19 ) ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
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
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('23',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X34 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('36',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_2 ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['22','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_2 ),
    inference(clc,[status(thm)],['34','35'])).

thf('39',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6EBmWp9gnh
% 0.16/0.38  % Computer   : n002.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 10:50:37 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 275 iterations in 0.097s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(t61_funct_2, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.54         ( m1_subset_1 @
% 0.35/0.54           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.54         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.54            ( m1_subset_1 @
% 0.35/0.54              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.54            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.35/0.54  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d4_funct_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.54       ( ![B:$i,C:$i]:
% 0.35/0.54         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.54             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.54               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.35/0.54             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.54               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.54         ((r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.35/0.54          | ((X21) = (k1_xboole_0))
% 0.35/0.54          | ((X21) != (k1_funct_1 @ X20 @ X19))
% 0.35/0.54          | ~ (v1_funct_1 @ X20)
% 0.35/0.54          | ~ (v1_relat_1 @ X20))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X20)
% 0.35/0.54          | ~ (v1_funct_1 @ X20)
% 0.35/0.54          | ((k1_funct_1 @ X20 @ X19) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ X19 @ (k1_relat_1 @ X20)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X19 @ X22) @ X20)
% 0.35/0.54          | ((X22) != (k1_funct_1 @ X20 @ X19))
% 0.35/0.54          | ~ (v1_funct_1 @ X20)
% 0.35/0.54          | ~ (v1_relat_1 @ X20))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X20)
% 0.35/0.54          | ~ (v1_funct_1 @ X20)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X19 @ (k1_funct_1 @ X20 @ X19)) @ X20)
% 0.35/0.54          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X20)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.35/0.54          | ~ (v1_funct_1 @ X0)
% 0.35/0.54          | ~ (v1_relat_1 @ X0)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.35/0.54          | ~ (v1_funct_1 @ X0)
% 0.35/0.54          | ~ (v1_relat_1 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '4'])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.35/0.54          | ~ (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_funct_1 @ X0)
% 0.35/0.54          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(l3_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X14 @ X15)
% 0.35/0.54          | (r2_hidden @ X14 @ X16)
% 0.35/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.35/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.35/0.54          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.35/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.35/0.54          | ~ (v1_relat_1 @ sk_C)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.35/0.54             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '9'])).
% 0.35/0.54  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( v1_relat_1 @ C ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.35/0.54         ((v1_relat_1 @ X25)
% 0.35/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.54  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.35/0.54             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.35/0.54  thf(t128_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( r2_hidden @
% 0.35/0.54         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.35/0.54       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.54         ((r2_hidden @ X10 @ X11)
% 0.35/0.54          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 0.35/0.54               (k2_zfmisc_1 @ (k1_tarski @ X8) @ X11)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2))),
% 0.35/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.54  thf('18', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('19', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ 
% 0.35/0.54             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.54         (((X9) = (X8))
% 0.35/0.54          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 0.35/0.54               (k2_zfmisc_1 @ (k1_tarski @ X8) @ X11)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0)) | ((X0) = (sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf(existence_m1_subset_1, axiom,
% 0.35/0.54    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.35/0.54  thf('23', plain, (![X13 : $i]: (m1_subset_1 @ (sk_B @ X13) @ X13)),
% 0.35/0.54      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.35/0.54  thf(t2_subset, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X17 : $i, X18 : $i]:
% 0.35/0.54         ((r2_hidden @ X17 @ X18)
% 0.35/0.54          | (v1_xboole_0 @ X18)
% 0.35/0.54          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t7_funct_2, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54       ( ( r2_hidden @ C @ A ) =>
% 0.35/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.54           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X34 @ X35)
% 0.35/0.54          | ((X36) = (k1_xboole_0))
% 0.35/0.54          | ~ (v1_funct_1 @ X37)
% 0.35/0.54          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.35/0.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.35/0.54          | (r2_hidden @ (k1_funct_1 @ X37 @ X34) @ X36))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.35/0.54          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.35/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.35/0.54          | ((sk_B_2) = (k1_xboole_0))
% 0.35/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.54  thf('29', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.35/0.54          | ((sk_B_2) = (k1_xboole_0))
% 0.35/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.35/0.54  thf('32', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.35/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.35/0.54        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.35/0.54           sk_B_2))),
% 0.35/0.54      inference('sup-', [status(thm)], ['25', '33'])).
% 0.35/0.54  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.35/0.54  thf('35', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ sk_B_2)),
% 0.35/0.54      inference('clc', [status(thm)], ['34', '35'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (((r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.35/0.54        | ((sk_B @ (k1_tarski @ sk_A)) = (sk_A)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['22', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ sk_B_2)),
% 0.35/0.54      inference('clc', [status(thm)], ['34', '35'])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)
% 0.35/0.54        | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.35/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('40', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('41', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.35/0.54      inference('clc', [status(thm)], ['39', '40'])).
% 0.35/0.54  thf('42', plain, ($false),
% 0.35/0.54      inference('demod', [status(thm)], ['0', '19', '41'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
