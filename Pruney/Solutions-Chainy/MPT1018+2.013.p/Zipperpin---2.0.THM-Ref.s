%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8EQxH6kZBX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:58 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 400 expanded)
%              Number of leaves         :   28 ( 126 expanded)
%              Depth                    :   17
%              Number of atoms          :  587 (7118 expanded)
%              Number of equality atoms :   55 ( 542 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X23 ) @ ( k1_funct_1 @ X23 @ X20 ) )
        = X20 )
      | ~ ( v2_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','29','30','31'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_funct_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X11 @ X13 ) )
      | ( X12 = X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','29','30','31'])).

thf('42',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ sk_D @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','43'])).

thf('45',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('47',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_D = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['48'])).

thf('50',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('52',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8EQxH6kZBX
% 0.18/0.37  % Computer   : n025.cluster.edu
% 0.18/0.37  % Model      : x86_64 x86_64
% 0.18/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.37  % Memory     : 8042.1875MB
% 0.18/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.37  % CPULimit   : 60
% 0.18/0.37  % DateTime   : Tue Dec  1 17:02:06 EST 2020
% 0.18/0.37  % CPUTime    : 
% 0.18/0.37  % Running portfolio for 600 s
% 0.18/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.38  % Number of cores: 8
% 0.18/0.38  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.24/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.54  % Solved by: fo/fo7.sh
% 0.24/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.54  % done 98 iterations in 0.048s
% 0.24/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.54  % SZS output start Refutation
% 0.24/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.24/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.24/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.24/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.54  thf(t85_funct_2, conjecture,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.24/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.24/0.54       ( ( v2_funct_1 @ B ) =>
% 0.24/0.54         ( ![C:$i,D:$i]:
% 0.24/0.54           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.24/0.54               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.24/0.54             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.24/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.54    (~( ![A:$i,B:$i]:
% 0.24/0.54        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.24/0.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.24/0.54          ( ( v2_funct_1 @ B ) =>
% 0.24/0.54            ( ![C:$i,D:$i]:
% 0.24/0.54              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.24/0.54                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.24/0.54                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.24/0.54    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.24/0.54  thf('0', plain,
% 0.24/0.54      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('1', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(dt_k1_relset_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.54       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.54  thf('2', plain,
% 0.24/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.54         ((m1_subset_1 @ (k1_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X14))
% 0.24/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.24/0.54      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.24/0.54  thf('3', plain,
% 0.24/0.54      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.24/0.54        (k1_zfmisc_1 @ sk_A))),
% 0.24/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.54  thf('4', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.24/0.54  thf('5', plain,
% 0.24/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.54         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.24/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.24/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.24/0.54  thf('6', plain,
% 0.24/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.24/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.54  thf('7', plain,
% 0.24/0.54      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.54      inference('demod', [status(thm)], ['3', '6'])).
% 0.24/0.54  thf(t3_subset, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.54  thf('8', plain,
% 0.24/0.54      (![X4 : $i, X5 : $i]:
% 0.24/0.54         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.54  thf('9', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.24/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.54  thf(d10_xboole_0, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.54  thf('10', plain,
% 0.24/0.54      (![X0 : $i, X2 : $i]:
% 0.24/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.54  thf('11', plain,
% 0.24/0.54      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.24/0.54        | ((sk_A) = (k1_relat_1 @ sk_B_1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.54  thf('12', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('13', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(t32_funct_2, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.54       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.24/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.54           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.24/0.54             ( C ) ) ) ) ))).
% 0.24/0.54  thf('14', plain,
% 0.24/0.54      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X20 @ X21)
% 0.24/0.54          | ((X22) = (k1_xboole_0))
% 0.24/0.54          | ~ (v1_funct_1 @ X23)
% 0.24/0.54          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.24/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.24/0.54          | ((k1_funct_1 @ (k2_funct_1 @ X23) @ (k1_funct_1 @ X23 @ X20))
% 0.24/0.54              = (X20))
% 0.24/0.54          | ~ (v2_funct_1 @ X23))),
% 0.24/0.54      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.24/0.54  thf('15', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (~ (v2_funct_1 @ sk_B_1)
% 0.24/0.54          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.24/0.54              = (X0))
% 0.24/0.54          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.24/0.54          | ~ (v1_funct_1 @ sk_B_1)
% 0.24/0.54          | ((sk_A) = (k1_xboole_0))
% 0.24/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.54  thf('16', plain, ((v2_funct_1 @ sk_B_1)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('17', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('19', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.24/0.54            = (X0))
% 0.24/0.54          | ((sk_A) = (k1_xboole_0))
% 0.24/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.54      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.24/0.54  thf('20', plain,
% 0.24/0.54      ((((sk_A) = (k1_xboole_0))
% 0.24/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.24/0.54            = (sk_C_1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['12', '19'])).
% 0.24/0.54  thf('21', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('22', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.24/0.54            = (X0))
% 0.24/0.54          | ((sk_A) = (k1_xboole_0))
% 0.24/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.24/0.54      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.24/0.54  thf('23', plain,
% 0.24/0.54      ((((sk_A) = (k1_xboole_0))
% 0.24/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.24/0.54            = (sk_D)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.54  thf('24', plain,
% 0.24/0.54      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('25', plain,
% 0.24/0.54      ((((sk_A) = (k1_xboole_0))
% 0.24/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.24/0.54            = (sk_D)))),
% 0.24/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.24/0.54  thf('26', plain,
% 0.24/0.54      ((((sk_C_1) = (sk_D))
% 0.24/0.54        | ((sk_A) = (k1_xboole_0))
% 0.24/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.24/0.54      inference('sup+', [status(thm)], ['20', '25'])).
% 0.24/0.54  thf('27', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.24/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.24/0.54  thf('28', plain, (((sk_C_1) != (sk_D))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.54      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.24/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.54  thf('30', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.24/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.54  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.54      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.24/0.54  thf('32', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_B_1))),
% 0.24/0.54      inference('demod', [status(thm)], ['11', '29', '30', '31'])).
% 0.24/0.54  thf(d8_funct_1, axiom,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.54       ( ( v2_funct_1 @ A ) <=>
% 0.24/0.54         ( ![B:$i,C:$i]:
% 0.24/0.54           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.24/0.54               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.24/0.54               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.24/0.54             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.24/0.54  thf('33', plain,
% 0.24/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.24/0.54         (~ (v2_funct_1 @ X11)
% 0.24/0.54          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.24/0.54          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11))
% 0.24/0.54          | ((k1_funct_1 @ X11 @ X12) != (k1_funct_1 @ X11 @ X13))
% 0.24/0.54          | ((X12) = (X13))
% 0.24/0.54          | ~ (v1_funct_1 @ X11)
% 0.24/0.54          | ~ (v1_relat_1 @ X11))),
% 0.24/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.24/0.54  thf('34', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.24/0.54          | ~ (v1_relat_1 @ sk_B_1)
% 0.24/0.54          | ~ (v1_funct_1 @ sk_B_1)
% 0.24/0.54          | ((X0) = (X1))
% 0.24/0.54          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.24/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.24/0.54          | ~ (v2_funct_1 @ sk_B_1))),
% 0.24/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.24/0.54  thf('35', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(cc2_relat_1, axiom,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ A ) =>
% 0.24/0.54       ( ![B:$i]:
% 0.24/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.24/0.54  thf('36', plain,
% 0.24/0.54      (![X7 : $i, X8 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.24/0.54          | (v1_relat_1 @ X7)
% 0.24/0.54          | ~ (v1_relat_1 @ X8))),
% 0.24/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.54  thf('37', plain,
% 0.24/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.24/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.24/0.54  thf(fc6_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.24/0.54  thf('38', plain,
% 0.24/0.54      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.24/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.54  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.24/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.24/0.54  thf('40', plain, ((v1_funct_1 @ sk_B_1)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('41', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_B_1))),
% 0.24/0.54      inference('demod', [status(thm)], ['11', '29', '30', '31'])).
% 0.24/0.54  thf('42', plain, ((v2_funct_1 @ sk_B_1)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('43', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.24/0.54          | ((X0) = (X1))
% 0.24/0.54          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.24/0.54          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.24/0.54      inference('demod', [status(thm)], ['34', '39', '40', '41', '42'])).
% 0.24/0.54  thf('44', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.24/0.54          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.24/0.54          | ((sk_D) = (X0))
% 0.24/0.54          | ~ (r2_hidden @ sk_D @ k1_xboole_0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['0', '43'])).
% 0.24/0.54  thf('45', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('46', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.54      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.24/0.54  thf('47', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.24/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.24/0.54  thf('48', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.24/0.54          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.24/0.54          | ((sk_D) = (X0)))),
% 0.24/0.54      inference('demod', [status(thm)], ['44', '47'])).
% 0.24/0.54  thf('49', plain,
% 0.24/0.54      ((((sk_D) = (sk_C_1)) | ~ (r2_hidden @ sk_C_1 @ k1_xboole_0))),
% 0.24/0.54      inference('eq_res', [status(thm)], ['48'])).
% 0.24/0.54  thf('50', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.24/0.54      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.24/0.54  thf('52', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.24/0.54      inference('demod', [status(thm)], ['50', '51'])).
% 0.24/0.54  thf('53', plain, (((sk_D) = (sk_C_1))),
% 0.24/0.54      inference('demod', [status(thm)], ['49', '52'])).
% 0.24/0.54  thf('54', plain, (((sk_C_1) != (sk_D))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('55', plain, ($false),
% 0.24/0.54      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.24/0.54  
% 0.24/0.54  % SZS output end Refutation
% 0.24/0.54  
% 0.24/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
