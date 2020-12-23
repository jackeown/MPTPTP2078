%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E1eERDmEPI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:20 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 106 expanded)
%              Number of leaves         :   40 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  600 ( 962 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B ) ),
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
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X51: $i,X52: $i] :
      ( ( zip_tseitin_1 @ X51 @ X52 )
      | ( X51 = k1_xboole_0 ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
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
    zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k1_relset_1 @ X46 @ X47 @ X45 )
        = ( k1_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['3','15','18'])).

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

thf('20',plain,(
    ! [X31: $i,X33: $i,X35: $i,X36: $i] :
      ( ( X33
       != ( k2_relat_1 @ X31 ) )
      | ( r2_hidden @ X35 @ X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X31 ) )
      | ( X35
       != ( k1_funct_1 @ X31 @ X36 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X31: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X31 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X31 @ X36 ) @ ( k2_relat_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf('28',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X42 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_relset_1 @ X49 @ X50 @ X48 )
        = ( k2_relat_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('41',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('42',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E1eERDmEPI
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 217 iterations in 0.221s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.64  thf(t65_funct_2, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.45/0.64         ( m1_subset_1 @
% 0.45/0.64           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.45/0.64       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.45/0.64            ( m1_subset_1 @
% 0.45/0.64              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.45/0.64          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.45/0.64  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(d1_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.64           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.64             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.64         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.64           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.64             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_1, axiom,
% 0.45/0.64    (![C:$i,B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.45/0.64       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.45/0.64         (~ (v1_funct_2 @ X55 @ X53 @ X54)
% 0.45/0.64          | ((X53) = (k1_relset_1 @ X53 @ X54 @ X55))
% 0.45/0.64          | ~ (zip_tseitin_2 @ X55 @ X54 @ X53))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.45/0.64        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_4, axiom,
% 0.45/0.64    (![B:$i,A:$i]:
% 0.45/0.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.64       ( zip_tseitin_1 @ B @ A ) ))).
% 0.45/0.64  thf(zf_stmt_5, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.45/0.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.45/0.64         (~ (zip_tseitin_1 @ X56 @ X57)
% 0.45/0.64          | (zip_tseitin_2 @ X58 @ X56 @ X57)
% 0.45/0.64          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.45/0.64        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X51 : $i, X52 : $i]:
% 0.45/0.64         ((zip_tseitin_1 @ X51 @ X52) | ((X51) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.45/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.64  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.45/0.64      inference('sup+', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf(d1_tarski, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.64         (((X14) != (X13))
% 0.45/0.64          | (r2_hidden @ X14 @ X15)
% 0.45/0.64          | ((X15) != (k1_tarski @ X13)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.64  thf('11', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.45/0.64      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.64  thf(t7_ordinal1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X37 : $i, X38 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 0.45/0.64      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.64  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.45/0.64      inference('sup-', [status(thm)], ['9', '13'])).
% 0.45/0.64  thf('15', plain, ((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.45/0.64      inference('demod', [status(thm)], ['6', '14'])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.64         (((k1_relset_1 @ X46 @ X47 @ X45) = (k1_relat_1 @ X45))
% 0.45/0.64          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.45/0.64         = (k1_relat_1 @ sk_D_2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.45/0.64      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.45/0.64  thf(d5_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.64               ( ?[D:$i]:
% 0.45/0.64                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.45/0.64                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X31 : $i, X33 : $i, X35 : $i, X36 : $i]:
% 0.45/0.64         (((X33) != (k2_relat_1 @ X31))
% 0.45/0.64          | (r2_hidden @ X35 @ X33)
% 0.45/0.64          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ X31))
% 0.45/0.64          | ((X35) != (k1_funct_1 @ X31 @ X36))
% 0.45/0.64          | ~ (v1_funct_1 @ X31)
% 0.45/0.64          | ~ (v1_relat_1 @ X31))),
% 0.45/0.64      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X31 : $i, X36 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X31)
% 0.45/0.64          | ~ (v1_funct_1 @ X31)
% 0.45/0.64          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ X31))
% 0.45/0.64          | (r2_hidden @ (k1_funct_1 @ X31 @ X36) @ (k2_relat_1 @ X31)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.64          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.45/0.64          | ~ (v1_funct_1 @ sk_D_2)
% 0.45/0.64          | ~ (v1_relat_1 @ sk_D_2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['19', '21'])).
% 0.45/0.64  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( v1_relat_1 @ C ) ))).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X39)
% 0.45/0.64          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 0.45/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.64          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['0', '27'])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_k2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (k2_relset_1 @ X42 @ X43 @ X44) @ (k1_zfmisc_1 @ X43))
% 0.45/0.64          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_2 @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X49 @ X50 @ X48) = (k2_relat_1 @ X48))
% 0.45/0.64          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.45/0.64         = (k2_relat_1 @ sk_D_2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['31', '34'])).
% 0.45/0.64  thf(t4_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.64       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X27 @ X28)
% 0.45/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.45/0.64          | (m1_subset_1 @ X27 @ X29))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B))
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      ((m1_subset_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['28', '37'])).
% 0.45/0.64  thf(t2_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.64       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X25 : $i, X26 : $i]:
% 0.45/0.64         ((r2_hidden @ X25 @ X26)
% 0.45/0.64          | (v1_xboole_0 @ X26)
% 0.45/0.64          | ~ (m1_subset_1 @ X25 @ X26))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.45/0.64        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.64  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.45/0.64  thf('41', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B))),
% 0.45/0.64      inference('clc', [status(thm)], ['40', '41'])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X16 @ X15)
% 0.45/0.64          | ((X16) = (X13))
% 0.45/0.64          | ((X15) != (k1_tarski @ X13)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (![X13 : $i, X16 : $i]:
% 0.45/0.64         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.45/0.64  thf('45', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) = (sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['42', '44'])).
% 0.45/0.64  thf('46', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) != (sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('47', plain, ($false),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
