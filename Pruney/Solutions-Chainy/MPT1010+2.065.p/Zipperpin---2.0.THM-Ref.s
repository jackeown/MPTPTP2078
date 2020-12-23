%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.at8viPQj0b

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:22 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 106 expanded)
%              Number of leaves         :   45 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  676 ( 984 expanded)
%              Number of equality atoms :   45 (  59 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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
    r2_hidden @ sk_C @ sk_A ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_2 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_1 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_1 @ X45 @ X46 )
      | ( zip_tseitin_2 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X18 @ X23 )
      | ( X23
       != ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X18 @ ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('23',plain,(
    ! [X12: $i,X14: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','24','27'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( X31
       != ( k1_funct_1 @ X30 @ X29 ) )
      | ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( r2_hidden @ ( k4_tarski @ X29 @ ( k1_funct_1 @ X30 @ X29 ) ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9 = X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ ( k1_tarski @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('43',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.at8viPQj0b
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 118 iterations in 0.165s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.40/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.40/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
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
% 0.40/0.61  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
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
% 0.40/0.61      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.40/0.61         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.40/0.61          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.40/0.61          | ~ (zip_tseitin_2 @ X44 @ X43 @ X42))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.61  thf(zf_stmt_2, axiom,
% 0.40/0.61    (![B:$i,A:$i]:
% 0.40/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X40 : $i, X41 : $i]:
% 0.40/0.61         ((zip_tseitin_1 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.61  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.40/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.40/0.61  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.40/0.61  thf(zf_stmt_5, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.40/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.61         (~ (zip_tseitin_1 @ X45 @ X46)
% 0.40/0.61          | (zip_tseitin_2 @ X47 @ X45 @ X46)
% 0.40/0.61          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.61        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.40/0.61          | (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['6', '9'])).
% 0.40/0.61  thf(t69_enumset1, axiom,
% 0.40/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.61  thf('11', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.61  thf(t70_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X2 : $i, X3 : $i]:
% 0.40/0.61         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.61  thf(t71_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.40/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.61  thf(d2_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.61     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.40/0.61       ( ![F:$i]:
% 0.40/0.61         ( ( r2_hidden @ F @ E ) <=>
% 0.40/0.61           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.40/0.61                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.40/0.61  thf(zf_stmt_7, axiom,
% 0.40/0.61    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.40/0.61     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.40/0.61       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.40/0.61         ( ( F ) != ( D ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_8, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.61     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.40/0.61       ( ![F:$i]:
% 0.40/0.61         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.61         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.40/0.61          | (r2_hidden @ X18 @ X23)
% 0.40/0.61          | ((X23) != (k2_enumset1 @ X22 @ X21 @ X20 @ X19)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.61         ((r2_hidden @ X18 @ (k2_enumset1 @ X22 @ X21 @ X20 @ X19))
% 0.40/0.61          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.40/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.61  thf(t7_ordinal1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X32 : $i, X33 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.61         ((zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3)
% 0.40/0.61          | ~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.40/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.61         (~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.40/0.61          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.40/0.61      inference('sup-', [status(thm)], ['13', '17'])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.40/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['12', '18'])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.40/0.61          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['11', '19'])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.40/0.61          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['10', '20'])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.61         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.61         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12)),
% 0.40/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.40/0.61  thf('24', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.40/0.61      inference('sup-', [status(thm)], ['21', '23'])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.61         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.40/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.40/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.61  thf('28', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.40/0.61      inference('demod', [status(thm)], ['3', '24', '27'])).
% 0.40/0.61  thf(t8_funct_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.61       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.40/0.61         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.40/0.61           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.40/0.61          | ((X31) != (k1_funct_1 @ X30 @ X29))
% 0.40/0.61          | (r2_hidden @ (k4_tarski @ X29 @ X31) @ X30)
% 0.40/0.61          | ~ (v1_funct_1 @ X30)
% 0.40/0.61          | ~ (v1_relat_1 @ X30))),
% 0.40/0.61      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X29 : $i, X30 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X30)
% 0.40/0.61          | ~ (v1_funct_1 @ X30)
% 0.40/0.61          | (r2_hidden @ (k4_tarski @ X29 @ (k1_funct_1 @ X30 @ X29)) @ X30)
% 0.40/0.61          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ X30)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.61          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D)
% 0.40/0.61          | ~ (v1_funct_1 @ sk_D)
% 0.40/0.61          | ~ (v1_relat_1 @ sk_D))),
% 0.40/0.61      inference('sup-', [status(thm)], ['28', '30'])).
% 0.40/0.61  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(cc1_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( v1_relat_1 @ C ) ))).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.40/0.61         ((v1_relat_1 @ X34)
% 0.40/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.61  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.61          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D))),
% 0.40/0.61      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ sk_D)),
% 0.40/0.61      inference('sup-', [status(thm)], ['0', '36'])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(l3_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X26 @ X27)
% 0.40/0.61          | (r2_hidden @ X26 @ X28)
% 0.40/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.40/0.61      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.40/0.61          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.40/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ 
% 0.40/0.61        (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['37', '40'])).
% 0.40/0.61  thf(t129_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.61     ( ( r2_hidden @
% 0.40/0.61         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.40/0.61       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.61         (((X9) = (X10))
% 0.40/0.61          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ 
% 0.40/0.61               (k2_zfmisc_1 @ X8 @ (k1_tarski @ X10))))),
% 0.40/0.61      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.40/0.61  thf('43', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.61  thf('44', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('45', plain, ($false),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
