%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bppMehoaCt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:26 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 118 expanded)
%              Number of leaves         :   43 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  584 ( 984 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ( X51
        = ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ~ ( zip_tseitin_2 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_1 @ X54 @ X55 )
      | ( zip_tseitin_2 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_1 @ X49 @ X50 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k1_relset_1 @ X47 @ X48 @ X46 )
        = ( k1_relat_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','15','18'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('20',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k1_relat_1 @ X40 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X40 @ X39 ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X37: $i,X38: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['21','26','27'])).

thf('29',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v5_relat_1 @ X43 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v5_relat_1 @ X35 @ X36 )
      | ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('44',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bppMehoaCt
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 139 iterations in 0.123s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.38/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.58  thf(t65_funct_2, conjecture,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @
% 0.38/0.58           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.38/0.58       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.38/0.58            ( m1_subset_1 @
% 0.38/0.58              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.38/0.58          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.38/0.58  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(d1_funct_2, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_1, axiom,
% 0.38/0.58    (![C:$i,B:$i,A:$i]:
% 0.38/0.58     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.38/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.38/0.58         (~ (v1_funct_2 @ X53 @ X51 @ X52)
% 0.38/0.58          | ((X51) = (k1_relset_1 @ X51 @ X52 @ X53))
% 0.38/0.58          | ~ (zip_tseitin_2 @ X53 @ X52 @ X51))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.38/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ 
% 0.38/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.38/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.38/0.58  thf(zf_stmt_4, axiom,
% 0.38/0.58    (![B:$i,A:$i]:
% 0.38/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.58       ( zip_tseitin_1 @ B @ A ) ))).
% 0.38/0.58  thf(zf_stmt_5, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.38/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.38/0.58         (~ (zip_tseitin_1 @ X54 @ X55)
% 0.38/0.58          | (zip_tseitin_2 @ X56 @ X54 @ X55)
% 0.38/0.58          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.38/0.58        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X49 : $i, X50 : $i]:
% 0.38/0.58         ((zip_tseitin_1 @ X49 @ X50) | ((X49) = (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.58  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.38/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf(d1_tarski, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.58         (((X14) != (X13))
% 0.38/0.58          | (r2_hidden @ X14 @ X15)
% 0.38/0.58          | ((X15) != (k1_tarski @ X13)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.58  thf('11', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.38/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.58  thf(t7_ordinal1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X41 : $i, X42 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X41 @ X42) | ~ (r1_tarski @ X42 @ X41))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.58  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '13'])).
% 0.38/0.58  thf('15', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.38/0.58      inference('demod', [status(thm)], ['6', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ 
% 0.38/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.38/0.58         (((k1_relset_1 @ X47 @ X48 @ X46) = (k1_relat_1 @ X46))
% 0.38/0.58          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.58  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.58      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.38/0.58  thf(t12_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.58       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.58         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X39 : $i, X40 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X39 @ (k1_relat_1 @ X40))
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ X40 @ X39) @ (k2_relat_1 @ X40))
% 0.38/0.58          | ~ (v1_funct_1 @ X40)
% 0.38/0.58          | ~ (v1_relat_1 @ X40))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.58          | ~ (v1_relat_1 @ sk_D)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_D)
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ 
% 0.38/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc2_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X33 : $i, X34 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.38/0.58          | (v1_relat_1 @ X33)
% 0.38/0.58          | ~ (v1_relat_1 @ X34))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.38/0.58        | (v1_relat_1 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf(fc6_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X37 : $i, X38 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X37 @ X38))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.58  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.58  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.38/0.58      inference('demod', [status(thm)], ['21', '26', '27'])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '28'])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D @ 
% 0.38/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc2_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.38/0.58         ((v5_relat_1 @ X43 @ X45)
% 0.38/0.58          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.58  thf('32', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf(d19_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X35 : $i, X36 : $i]:
% 0.38/0.58         (~ (v5_relat_1 @ X35 @ X36)
% 0.38/0.58          | (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 0.38/0.58          | ~ (v1_relat_1 @ X35))),
% 0.38/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_D)
% 0.38/0.58        | (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_tarski @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.58  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_tarski @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf(t3_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (![X27 : $i, X29 : $i]:
% 0.38/0.58         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf(t4_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X30 @ X31)
% 0.38/0.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.38/0.58          | (m1_subset_1 @ X30 @ X32))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['29', '40'])).
% 0.38/0.58  thf(t2_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i]:
% 0.38/0.58         ((r2_hidden @ X25 @ X26)
% 0.38/0.58          | (v1_xboole_0 @ X26)
% 0.38/0.58          | ~ (m1_subset_1 @ X25 @ X26))),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.38/0.58        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.58  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.38/0.58  thf('44', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X24))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.38/0.58      inference('clc', [status(thm)], ['43', '44'])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X16 @ X15)
% 0.38/0.58          | ((X16) = (X13))
% 0.38/0.58          | ((X15) != (k1_tarski @ X13)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (![X13 : $i, X16 : $i]:
% 0.38/0.58         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.38/0.58  thf('48', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['45', '47'])).
% 0.38/0.58  thf('49', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('50', plain, ($false),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
