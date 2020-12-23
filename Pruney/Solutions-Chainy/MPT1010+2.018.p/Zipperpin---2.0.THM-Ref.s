%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MdYGRxopxW

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:15 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 134 expanded)
%              Number of leaves         :   48 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  807 (1240 expanded)
%              Number of equality atoms :   53 (  77 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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

thf(zf_stmt_0,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 )
      | ( X12 = X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_2 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_1 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_1 @ X45 @ X46 )
      | ( zip_tseitin_2 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('10',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X17 @ X22 )
      | ( X22
       != ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X17 @ ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X11: $i,X13: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X15 @ X11 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','25','28'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X27 ) @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v5_relat_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X18 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X18 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C_1 )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C_1 )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C_1 )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','56'])).

thf('58',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MdYGRxopxW
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:07:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.21/0.34  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 194 iterations in 0.138s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.42/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.42/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.42/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(d2_enumset1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.42/0.59     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.42/0.59       ( ![F:$i]:
% 0.42/0.59         ( ( r2_hidden @ F @ E ) <=>
% 0.42/0.59           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.42/0.59                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, axiom,
% 0.42/0.59    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.42/0.59     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.42/0.59       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.42/0.59         ( ( F ) != ( D ) ) ) ))).
% 0.42/0.59  thf('0', plain,
% 0.42/0.59      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.42/0.59          | ((X12) = (X13))
% 0.42/0.59          | ((X12) = (X14))
% 0.42/0.59          | ((X12) = (X15))
% 0.42/0.59          | ((X12) = (X16)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t65_funct_2, conjecture,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.59         ( m1_subset_1 @
% 0.42/0.59           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.59       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_1, negated_conjecture,
% 0.42/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.59            ( m1_subset_1 @
% 0.42/0.59              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.59          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.42/0.59  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('2', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf(d1_funct_2, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_2, axiom,
% 0.42/0.59    (![C:$i,B:$i,A:$i]:
% 0.42/0.59     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.42/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.59  thf('3', plain,
% 0.42/0.59      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.42/0.59         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.42/0.59          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.42/0.59          | ~ (zip_tseitin_2 @ X44 @ X43 @ X42))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.42/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.59  thf(zf_stmt_3, axiom,
% 0.42/0.59    (![B:$i,A:$i]:
% 0.42/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59       ( zip_tseitin_1 @ B @ A ) ))).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X40 : $i, X41 : $i]:
% 0.42/0.59         ((zip_tseitin_1 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.59  thf('6', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.42/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.59  thf('7', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.42/0.59      inference('sup+', [status(thm)], ['5', '6'])).
% 0.42/0.59  thf('8', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_6, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.42/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.59  thf('9', plain,
% 0.42/0.59      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.42/0.59         (~ (zip_tseitin_1 @ X45 @ X46)
% 0.42/0.59          | (zip_tseitin_2 @ X47 @ X45 @ X46)
% 0.42/0.59          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.42/0.59        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.42/0.59          | (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['7', '10'])).
% 0.42/0.59  thf(t69_enumset1, axiom,
% 0.42/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.59  thf('12', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.42/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.59  thf(t70_enumset1, axiom,
% 0.42/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.59  thf('13', plain,
% 0.42/0.59      (![X6 : $i, X7 : $i]:
% 0.42/0.59         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.42/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.59  thf(t71_enumset1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.59         ((k2_enumset1 @ X8 @ X8 @ X9 @ X10) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.42/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.42/0.59  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_8, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.42/0.59     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.42/0.59       ( ![F:$i]:
% 0.42/0.59         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.42/0.59  thf('15', plain,
% 0.42/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.42/0.59          | (r2_hidden @ X17 @ X22)
% 0.42/0.59          | ((X22) != (k2_enumset1 @ X21 @ X20 @ X19 @ X18)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.42/0.59  thf('16', plain,
% 0.42/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.59         ((r2_hidden @ X17 @ (k2_enumset1 @ X21 @ X20 @ X19 @ X18))
% 0.42/0.59          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.42/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.59  thf(t7_ordinal1, axiom,
% 0.42/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      (![X29 : $i, X30 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.42/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.59  thf('18', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3)
% 0.42/0.59          | ~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.42/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.59  thf('19', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.59         (~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.42/0.59          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.42/0.59      inference('sup-', [status(thm)], ['14', '18'])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.42/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['13', '19'])).
% 0.42/0.59  thf('21', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.42/0.59          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['12', '20'])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.42/0.59          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['11', '21'])).
% 0.42/0.59  thf('23', plain,
% 0.42/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.59         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X11))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('24', plain,
% 0.42/0.59      (![X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.59         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X15 @ X11)),
% 0.42/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.42/0.59  thf('25', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.42/0.59      inference('sup-', [status(thm)], ['22', '24'])).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.59  thf('27', plain,
% 0.42/0.59      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.42/0.59         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.42/0.59          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.59  thf('28', plain,
% 0.42/0.59      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.42/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.59  thf('29', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.42/0.59      inference('demod', [status(thm)], ['4', '25', '28'])).
% 0.42/0.59  thf(t12_funct_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.59       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.59         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      (![X27 : $i, X28 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.42/0.59          | (r2_hidden @ (k1_funct_1 @ X28 @ X27) @ (k2_relat_1 @ X28))
% 0.42/0.59          | ~ (v1_funct_1 @ X28)
% 0.42/0.59          | ~ (v1_relat_1 @ X28))),
% 0.42/0.59      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.59          | ~ (v1_relat_1 @ sk_D)
% 0.42/0.59          | ~ (v1_funct_1 @ sk_D)
% 0.42/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf(cc1_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( v1_relat_1 @ C ) ))).
% 0.42/0.59  thf('33', plain,
% 0.42/0.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.42/0.59         ((v1_relat_1 @ X31)
% 0.42/0.59          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.59  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.59  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('36', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.42/0.59      inference('demod', [status(thm)], ['31', '34', '35'])).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.42/0.59      inference('sup-', [status(thm)], ['1', '36'])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf(cc2_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.59  thf('39', plain,
% 0.42/0.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.42/0.59         ((v5_relat_1 @ X34 @ X36)
% 0.42/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.42/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.59  thf('40', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.42/0.59  thf(d19_relat_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( v1_relat_1 @ B ) =>
% 0.42/0.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.59  thf('41', plain,
% 0.42/0.59      (![X25 : $i, X26 : $i]:
% 0.42/0.59         (~ (v5_relat_1 @ X25 @ X26)
% 0.42/0.59          | (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.42/0.59          | ~ (v1_relat_1 @ X25))),
% 0.42/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.42/0.59  thf('42', plain,
% 0.42/0.59      ((~ (v1_relat_1 @ sk_D)
% 0.42/0.59        | (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_tarski @ sk_B)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.42/0.59  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.59  thf('44', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_tarski @ sk_B))),
% 0.42/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.42/0.59  thf(d3_tarski, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.59  thf('45', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.42/0.59          | (r2_hidden @ X0 @ X2)
% 0.42/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.42/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.59  thf('46', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.42/0.59          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.59  thf('47', plain,
% 0.42/0.59      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['37', '46'])).
% 0.42/0.59  thf('48', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.42/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.59  thf('49', plain,
% 0.42/0.59      (![X6 : $i, X7 : $i]:
% 0.42/0.59         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.42/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.59  thf('50', plain,
% 0.42/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.59         ((k2_enumset1 @ X8 @ X8 @ X9 @ X10) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.42/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.42/0.59  thf('51', plain,
% 0.42/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X23 @ X22)
% 0.42/0.59          | ~ (zip_tseitin_0 @ X23 @ X18 @ X19 @ X20 @ X21)
% 0.42/0.59          | ((X22) != (k2_enumset1 @ X21 @ X20 @ X19 @ X18)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.42/0.59  thf('52', plain,
% 0.42/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.42/0.59         (~ (zip_tseitin_0 @ X23 @ X18 @ X19 @ X20 @ X21)
% 0.42/0.59          | ~ (r2_hidden @ X23 @ (k2_enumset1 @ X21 @ X20 @ X19 @ X18)))),
% 0.42/0.59      inference('simplify', [status(thm)], ['51'])).
% 0.42/0.59  thf('53', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.42/0.59          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.42/0.59      inference('sup-', [status(thm)], ['50', '52'])).
% 0.42/0.59  thf('54', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.59          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['49', '53'])).
% 0.42/0.59  thf('55', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.42/0.59          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['48', '54'])).
% 0.42/0.59  thf('56', plain,
% 0.42/0.59      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B @ sk_B @ sk_B @ 
% 0.42/0.59          sk_B)),
% 0.42/0.59      inference('sup-', [status(thm)], ['47', '55'])).
% 0.42/0.59  thf('57', plain,
% 0.42/0.59      ((((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))
% 0.42/0.59        | ((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))
% 0.42/0.59        | ((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))
% 0.42/0.59        | ((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['0', '56'])).
% 0.42/0.59  thf('58', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.42/0.59      inference('simplify', [status(thm)], ['57'])).
% 0.42/0.59  thf('59', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('60', plain, ($false),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
