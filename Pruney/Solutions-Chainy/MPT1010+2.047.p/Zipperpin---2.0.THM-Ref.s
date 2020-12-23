%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4FeZExUKH9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:19 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 101 expanded)
%              Number of leaves         :   38 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  570 ( 925 expanded)
%              Number of equality atoms :   35 (  51 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_funct_2 @ X55 @ X53 @ X54 )
      | ( X53
        = ( k1_relset_1 @ X53 @ X54 @ X55 ) )
      | ~ ( zip_tseitin_2 @ X55 @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( zip_tseitin_1 @ X56 @ X57 )
      | ( zip_tseitin_2 @ X58 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X51: $i,X52: $i] :
      ( ( zip_tseitin_1 @ X51 @ X52 )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k1_relset_1 @ X46 @ X47 @ X45 )
        = ( k1_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X33: $i,X35: $i,X37: $i,X38: $i] :
      ( ( X35
       != ( k2_relat_1 @ X33 ) )
      | ( r2_hidden @ X37 @ X35 )
      | ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X33 ) )
      | ( X37
       != ( k1_funct_1 @ X33 @ X38 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('18',plain,(
    ! [X33: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X33 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X38 ) @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X42 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_relset_1 @ X49 @ X50 @ X48 )
        = ( k2_relat_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('33',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( m1_subset_1 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( X18 = X15 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.08  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4FeZExUKH9
% 0.07/0.26  % Computer   : n009.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 17:00:41 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  % Running portfolio for 600 s
% 0.07/0.27  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.27  % Number of cores: 8
% 0.11/0.27  % Python version: Python 3.6.8
% 0.11/0.27  % Running in FO mode
% 0.11/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.11/0.56  % Solved by: fo/fo7.sh
% 0.11/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.11/0.56  % done 202 iterations in 0.185s
% 0.11/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.11/0.56  % SZS output start Refutation
% 0.11/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.11/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.11/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.11/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.11/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.11/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.11/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.11/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.11/0.56  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.11/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.11/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.11/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.11/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.11/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.11/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.11/0.56  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.11/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.11/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.11/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.11/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.11/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.11/0.56  thf(t65_funct_2, conjecture,
% 0.11/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.11/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.11/0.56         ( m1_subset_1 @
% 0.11/0.56           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.11/0.56       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.11/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.11/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.11/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.11/0.56            ( m1_subset_1 @
% 0.11/0.56              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.11/0.56          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.11/0.56    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.11/0.56  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf(d1_funct_2, axiom,
% 0.11/0.56    (![A:$i,B:$i,C:$i]:
% 0.11/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.11/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.11/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.11/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.11/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.11/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.11/0.56  thf(zf_stmt_1, axiom,
% 0.11/0.56    (![C:$i,B:$i,A:$i]:
% 0.11/0.56     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.11/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.11/0.56  thf('2', plain,
% 0.11/0.56      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.11/0.56         (~ (v1_funct_2 @ X55 @ X53 @ X54)
% 0.11/0.56          | ((X53) = (k1_relset_1 @ X53 @ X54 @ X55))
% 0.11/0.56          | ~ (zip_tseitin_2 @ X55 @ X54 @ X53))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.11/0.56  thf('3', plain,
% 0.11/0.56      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.11/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)))),
% 0.11/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.11/0.56  thf('4', plain,
% 0.11/0.56      ((m1_subset_1 @ sk_D_2 @ 
% 0.11/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.11/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.11/0.56  thf(zf_stmt_4, axiom,
% 0.11/0.56    (![B:$i,A:$i]:
% 0.11/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.11/0.56       ( zip_tseitin_1 @ B @ A ) ))).
% 0.11/0.56  thf(zf_stmt_5, axiom,
% 0.11/0.56    (![A:$i,B:$i,C:$i]:
% 0.11/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.56       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.11/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.11/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.11/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.11/0.56  thf('5', plain,
% 0.11/0.56      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.11/0.56         (~ (zip_tseitin_1 @ X56 @ X57)
% 0.11/0.56          | (zip_tseitin_2 @ X58 @ X56 @ X57)
% 0.11/0.56          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56))))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.11/0.56  thf('6', plain,
% 0.11/0.56      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.11/0.56        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.11/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.11/0.56  thf('7', plain,
% 0.11/0.56      (![X51 : $i, X52 : $i]:
% 0.11/0.56         ((zip_tseitin_1 @ X51 @ X52) | ((X51) = (k1_xboole_0)))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.11/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.11/0.56  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.11/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.11/0.56  thf('9', plain,
% 0.11/0.56      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 0.11/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.11/0.56  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.11/0.56  thf('10', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X26))),
% 0.11/0.56      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.11/0.56  thf('11', plain,
% 0.11/0.56      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.11/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.11/0.56  thf('12', plain, ((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.11/0.56      inference('demod', [status(thm)], ['6', '11'])).
% 0.11/0.56  thf('13', plain,
% 0.11/0.56      ((m1_subset_1 @ sk_D_2 @ 
% 0.11/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.11/0.56    (![A:$i,B:$i,C:$i]:
% 0.11/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.11/0.56  thf('14', plain,
% 0.11/0.56      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.11/0.56         (((k1_relset_1 @ X46 @ X47 @ X45) = (k1_relat_1 @ X45))
% 0.11/0.56          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.11/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.11/0.56  thf('15', plain,
% 0.11/0.56      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 0.11/0.56         = (k1_relat_1 @ sk_D_2))),
% 0.11/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.11/0.56  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.11/0.56      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.11/0.56  thf(d5_funct_1, axiom,
% 0.11/0.56    (![A:$i]:
% 0.11/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.11/0.56       ( ![B:$i]:
% 0.11/0.56         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.11/0.56           ( ![C:$i]:
% 0.11/0.56             ( ( r2_hidden @ C @ B ) <=>
% 0.11/0.56               ( ?[D:$i]:
% 0.11/0.56                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.11/0.56                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.11/0.56  thf('17', plain,
% 0.11/0.56      (![X33 : $i, X35 : $i, X37 : $i, X38 : $i]:
% 0.11/0.56         (((X35) != (k2_relat_1 @ X33))
% 0.11/0.56          | (r2_hidden @ X37 @ X35)
% 0.11/0.56          | ~ (r2_hidden @ X38 @ (k1_relat_1 @ X33))
% 0.11/0.56          | ((X37) != (k1_funct_1 @ X33 @ X38))
% 0.11/0.56          | ~ (v1_funct_1 @ X33)
% 0.11/0.56          | ~ (v1_relat_1 @ X33))),
% 0.11/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.11/0.56  thf('18', plain,
% 0.11/0.56      (![X33 : $i, X38 : $i]:
% 0.11/0.56         (~ (v1_relat_1 @ X33)
% 0.11/0.56          | ~ (v1_funct_1 @ X33)
% 0.11/0.56          | ~ (r2_hidden @ X38 @ (k1_relat_1 @ X33))
% 0.11/0.56          | (r2_hidden @ (k1_funct_1 @ X33 @ X38) @ (k2_relat_1 @ X33)))),
% 0.11/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.11/0.56  thf('19', plain,
% 0.11/0.56      (![X0 : $i]:
% 0.11/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.11/0.56          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.11/0.56          | ~ (v1_funct_1 @ sk_D_2)
% 0.11/0.56          | ~ (v1_relat_1 @ sk_D_2))),
% 0.11/0.56      inference('sup-', [status(thm)], ['16', '18'])).
% 0.11/0.56  thf('20', plain, ((v1_funct_1 @ sk_D_2)),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf('21', plain,
% 0.11/0.56      ((m1_subset_1 @ sk_D_2 @ 
% 0.11/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf(cc1_relset_1, axiom,
% 0.11/0.56    (![A:$i,B:$i,C:$i]:
% 0.11/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.56       ( v1_relat_1 @ C ) ))).
% 0.11/0.56  thf('22', plain,
% 0.11/0.56      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.11/0.56         ((v1_relat_1 @ X39)
% 0.11/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.11/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.11/0.56  thf('23', plain, ((v1_relat_1 @ sk_D_2)),
% 0.11/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.11/0.56  thf('24', plain,
% 0.11/0.56      (![X0 : $i]:
% 0.11/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.11/0.56          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.11/0.56      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.11/0.56  thf('25', plain,
% 0.11/0.56      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))),
% 0.11/0.56      inference('sup-', [status(thm)], ['0', '24'])).
% 0.11/0.56  thf('26', plain,
% 0.11/0.56      ((m1_subset_1 @ sk_D_2 @ 
% 0.11/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf(dt_k2_relset_1, axiom,
% 0.11/0.56    (![A:$i,B:$i,C:$i]:
% 0.11/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.56       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.11/0.56  thf('27', plain,
% 0.11/0.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.11/0.56         ((m1_subset_1 @ (k2_relset_1 @ X42 @ X43 @ X44) @ (k1_zfmisc_1 @ X43))
% 0.11/0.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.11/0.56      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.11/0.56  thf('28', plain,
% 0.11/0.56      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2) @ 
% 0.11/0.56        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.11/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.11/0.56  thf('29', plain,
% 0.11/0.56      ((m1_subset_1 @ sk_D_2 @ 
% 0.11/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.11/0.56    (![A:$i,B:$i,C:$i]:
% 0.11/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.11/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.11/0.56  thf('30', plain,
% 0.11/0.56      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.11/0.56         (((k2_relset_1 @ X49 @ X50 @ X48) = (k2_relat_1 @ X48))
% 0.11/0.56          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 0.11/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.11/0.56  thf('31', plain,
% 0.11/0.56      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 0.11/0.56         = (k2_relat_1 @ sk_D_2))),
% 0.11/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.11/0.56  thf('32', plain,
% 0.11/0.56      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.11/0.56        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.11/0.56      inference('demod', [status(thm)], ['28', '31'])).
% 0.11/0.56  thf(t4_subset, axiom,
% 0.11/0.56    (![A:$i,B:$i,C:$i]:
% 0.11/0.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.11/0.56       ( m1_subset_1 @ A @ C ) ))).
% 0.11/0.56  thf('33', plain,
% 0.11/0.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.11/0.56         (~ (r2_hidden @ X29 @ X30)
% 0.11/0.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.11/0.56          | (m1_subset_1 @ X29 @ X31))),
% 0.11/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.11/0.56  thf('34', plain,
% 0.11/0.56      (![X0 : $i]:
% 0.11/0.56         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.11/0.56          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.11/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.11/0.56  thf('35', plain,
% 0.11/0.56      ((m1_subset_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B_1))),
% 0.11/0.56      inference('sup-', [status(thm)], ['25', '34'])).
% 0.11/0.56  thf(t2_subset, axiom,
% 0.11/0.56    (![A:$i,B:$i]:
% 0.11/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.11/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.11/0.56  thf('36', plain,
% 0.11/0.56      (![X27 : $i, X28 : $i]:
% 0.11/0.56         ((r2_hidden @ X27 @ X28)
% 0.11/0.56          | (v1_xboole_0 @ X28)
% 0.11/0.56          | ~ (m1_subset_1 @ X27 @ X28))),
% 0.11/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.11/0.56  thf('37', plain,
% 0.11/0.56      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.11/0.56        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B_1)))),
% 0.11/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.11/0.56  thf('38', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X26))),
% 0.11/0.56      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.11/0.56  thf('39', plain,
% 0.11/0.56      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B_1))),
% 0.11/0.56      inference('clc', [status(thm)], ['37', '38'])).
% 0.11/0.56  thf(d1_tarski, axiom,
% 0.11/0.56    (![A:$i,B:$i]:
% 0.11/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.11/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.11/0.56  thf('40', plain,
% 0.11/0.56      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.11/0.56         (~ (r2_hidden @ X18 @ X17)
% 0.11/0.56          | ((X18) = (X15))
% 0.11/0.56          | ((X17) != (k1_tarski @ X15)))),
% 0.11/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.11/0.56  thf('41', plain,
% 0.11/0.56      (![X15 : $i, X18 : $i]:
% 0.11/0.56         (((X18) = (X15)) | ~ (r2_hidden @ X18 @ (k1_tarski @ X15)))),
% 0.11/0.56      inference('simplify', [status(thm)], ['40'])).
% 0.11/0.56  thf('42', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) = (sk_B_1))),
% 0.11/0.56      inference('sup-', [status(thm)], ['39', '41'])).
% 0.11/0.56  thf('43', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) != (sk_B_1))),
% 0.11/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.56  thf('44', plain, ($false),
% 0.11/0.56      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.11/0.56  
% 0.11/0.56  % SZS output end Refutation
% 0.11/0.56  
% 0.11/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
