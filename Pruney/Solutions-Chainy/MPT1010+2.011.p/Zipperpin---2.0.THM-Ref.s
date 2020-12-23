%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.acFNRNTL0c

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:14 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 110 expanded)
%              Number of leaves         :   40 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  589 ( 974 expanded)
%              Number of equality atoms :   36 (  54 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    r2_hidden @ sk_C_3 @ sk_A ),
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
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v1_funct_2 @ X60 @ X58 @ X59 )
      | ( X58
        = ( k1_relset_1 @ X58 @ X59 @ X60 ) )
      | ~ ( zip_tseitin_2 @ X60 @ X59 @ X58 ) ) ),
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
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( zip_tseitin_1 @ X61 @ X62 )
      | ( zip_tseitin_2 @ X63 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X56: $i,X57: $i] :
      ( ( zip_tseitin_1 @ X56 @ X57 )
      | ( X56 = k1_xboole_0 ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( r1_tarski @ X46 @ X45 ) ) ),
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
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k1_relset_1 @ X54 @ X55 @ X53 )
        = ( k1_relat_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
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
    ! [X39: $i,X41: $i,X43: $i,X44: $i] :
      ( ( X41
       != ( k2_relat_1 @ X39 ) )
      | ( r2_hidden @ X43 @ X41 )
      | ~ ( r2_hidden @ X44 @ ( k1_relat_1 @ X39 ) )
      | ( X43
       != ( k1_funct_1 @ X39 @ X44 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X39: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( r2_hidden @ X44 @ ( k1_relat_1 @ X39 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X39 @ X44 ) @ ( k2_relat_1 @ X39 ) ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v1_relat_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
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
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_3 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( v5_relat_1 @ X50 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v5_relat_1 @ X36 @ X37 )
      | ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X34 @ X35 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('40',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('41',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['28','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_3 )
    = sk_B ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_3 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.acFNRNTL0c
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 326 iterations in 0.154s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.40/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(t65_funct_2, conjecture,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.40/0.61         ( m1_subset_1 @
% 0.40/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.40/0.61       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.40/0.61            ( m1_subset_1 @
% 0.40/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.40/0.61          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.40/0.61  thf('0', plain, ((r2_hidden @ sk_C_3 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(d1_funct_2, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_1, axiom,
% 0.40/0.61    (![C:$i,B:$i,A:$i]:
% 0.40/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.40/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.40/0.61         (~ (v1_funct_2 @ X60 @ X58 @ X59)
% 0.40/0.61          | ((X58) = (k1_relset_1 @ X58 @ X59 @ X60))
% 0.40/0.61          | ~ (zip_tseitin_2 @ X60 @ X59 @ X58))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.40/0.61  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.40/0.61  thf(zf_stmt_4, axiom,
% 0.40/0.61    (![B:$i,A:$i]:
% 0.40/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.40/0.61  thf(zf_stmt_5, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.40/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.40/0.61         (~ (zip_tseitin_1 @ X61 @ X62)
% 0.40/0.61          | (zip_tseitin_2 @ X63 @ X61 @ X62)
% 0.40/0.61          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.61        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X56 : $i, X57 : $i]:
% 0.40/0.61         ((zip_tseitin_1 @ X56 @ X57) | ((X56) = (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.40/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.61  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.40/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.40/0.61  thf(d1_tarski, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.61         (((X2) != (X1)) | (r2_hidden @ X2 @ X3) | ((X3) != (k1_tarski @ X1)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.61  thf('11', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.61  thf(t7_ordinal1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X45 : $i, X46 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X45 @ X46) | ~ (r1_tarski @ X46 @ X45))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.61  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.40/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.40/0.61      inference('sup-', [status(thm)], ['9', '13'])).
% 0.40/0.61  thf('15', plain, ((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.40/0.61      inference('demod', [status(thm)], ['6', '14'])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.40/0.61         (((k1_relset_1 @ X54 @ X55 @ X53) = (k1_relat_1 @ X53))
% 0.40/0.61          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.40/0.61         = (k1_relat_1 @ sk_D_2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.61  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.40/0.61      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.40/0.61  thf(d5_funct_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.40/0.61           ( ![C:$i]:
% 0.40/0.61             ( ( r2_hidden @ C @ B ) <=>
% 0.40/0.61               ( ?[D:$i]:
% 0.40/0.61                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.40/0.61                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X39 : $i, X41 : $i, X43 : $i, X44 : $i]:
% 0.40/0.61         (((X41) != (k2_relat_1 @ X39))
% 0.40/0.61          | (r2_hidden @ X43 @ X41)
% 0.40/0.61          | ~ (r2_hidden @ X44 @ (k1_relat_1 @ X39))
% 0.40/0.61          | ((X43) != (k1_funct_1 @ X39 @ X44))
% 0.40/0.61          | ~ (v1_funct_1 @ X39)
% 0.40/0.61          | ~ (v1_relat_1 @ X39))),
% 0.40/0.61      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X39 : $i, X44 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X39)
% 0.40/0.61          | ~ (v1_funct_1 @ X39)
% 0.40/0.61          | ~ (r2_hidden @ X44 @ (k1_relat_1 @ X39))
% 0.40/0.61          | (r2_hidden @ (k1_funct_1 @ X39 @ X44) @ (k2_relat_1 @ X39)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.40/0.61          | ~ (v1_funct_1 @ sk_D_2)
% 0.40/0.61          | ~ (v1_relat_1 @ sk_D_2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['19', '21'])).
% 0.40/0.61  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(cc1_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( v1_relat_1 @ C ) ))).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.40/0.61         ((v1_relat_1 @ X47)
% 0.40/0.61          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.61  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 0.40/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.61          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_3) @ (k2_relat_1 @ sk_D_2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['0', '27'])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D_2 @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(cc2_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.40/0.61         ((v5_relat_1 @ X50 @ X52)
% 0.40/0.61          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.61  thf('31', plain, ((v5_relat_1 @ sk_D_2 @ (k1_tarski @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf(d19_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      (![X36 : $i, X37 : $i]:
% 0.40/0.61         (~ (v5_relat_1 @ X36 @ X37)
% 0.40/0.61          | (r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 0.40/0.61          | ~ (v1_relat_1 @ X36))),
% 0.40/0.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      ((~ (v1_relat_1 @ sk_D_2)
% 0.40/0.61        | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.61  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.40/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.61  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.40/0.61  thf(d1_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.61         (~ (r1_tarski @ X12 @ X13)
% 0.40/0.61          | (r2_hidden @ X12 @ X14)
% 0.40/0.61          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      (![X12 : $i, X13 : $i]:
% 0.40/0.61         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 0.40/0.61      inference('simplify', [status(thm)], ['36'])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      ((r2_hidden @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['35', '37'])).
% 0.40/0.61  thf(t1_subset, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      (![X34 : $i, X35 : $i]:
% 0.40/0.61         ((m1_subset_1 @ X34 @ X35) | ~ (r2_hidden @ X34 @ X35))),
% 0.40/0.61      inference('cnf', [status(esa)], [t1_subset])).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.61  thf(l3_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X31 @ X32)
% 0.40/0.61          | (r2_hidden @ X31 @ X33)
% 0.40/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 0.40/0.61      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.40/0.61          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_3) @ (k1_tarski @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['28', '42'])).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (![X1 : $i, X4 : $i]:
% 0.40/0.61         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.61  thf('46', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_3) = (sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['43', '45'])).
% 0.40/0.61  thf('47', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_3) != (sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('48', plain, ($false),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
