%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SmmryyaZ8Z

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:23 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 110 expanded)
%              Number of leaves         :   47 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  748 (1056 expanded)
%              Number of equality atoms :   51 (  65 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_2 @ X51 @ X50 @ X49 ) ) ),
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
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_1 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_1 @ X52 @ X53 )
      | ( zip_tseitin_2 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
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

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X23 @ X29 )
      | ( X29
       != ( k3_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X23 @ ( k3_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('25',plain,(
    ! [X16: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X20 @ X21 @ X16 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X46 @ X44 )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','26','29'])).

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

thf('31',plain,(
    ! [X35: $i,X36: $i,X38: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( r2_hidden @ ( k4_tarski @ X35 @ X38 ) @ X36 )
      | ( X38
       != ( k1_funct_1 @ X36 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ( r2_hidden @ ( k4_tarski @ X35 @ ( k1_funct_1 @ X36 @ X35 ) ) @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('41',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ ( k1_tarski @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('45',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SmmryyaZ8Z
% 0.14/0.37  % Computer   : n007.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:13:06 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.35/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.61  % Solved by: fo/fo7.sh
% 0.35/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.61  % done 103 iterations in 0.130s
% 0.35/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.61  % SZS output start Refutation
% 0.35/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.35/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.35/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.35/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.35/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.35/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.35/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.61  thf(t65_funct_2, conjecture,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.35/0.61         ( m1_subset_1 @
% 0.35/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.35/0.61       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.35/0.61            ( m1_subset_1 @
% 0.35/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.35/0.61          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.35/0.61    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.35/0.61  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(d1_funct_2, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_1, axiom,
% 0.35/0.61    (![C:$i,B:$i,A:$i]:
% 0.35/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.35/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.61  thf('2', plain,
% 0.35/0.61      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.35/0.61         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 0.35/0.61          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 0.35/0.61          | ~ (zip_tseitin_2 @ X51 @ X50 @ X49))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.61  thf('3', plain,
% 0.35/0.61      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.61  thf(zf_stmt_2, axiom,
% 0.35/0.61    (![B:$i,A:$i]:
% 0.35/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.35/0.61  thf('4', plain,
% 0.35/0.61      (![X47 : $i, X48 : $i]:
% 0.35/0.61         ((zip_tseitin_1 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.61  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.61  thf('6', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.35/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.35/0.61  thf('7', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_D @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.35/0.61  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.35/0.61  thf(zf_stmt_5, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.35/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.61  thf('8', plain,
% 0.35/0.61      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.35/0.61         (~ (zip_tseitin_1 @ X52 @ X53)
% 0.35/0.61          | (zip_tseitin_2 @ X54 @ X52 @ X53)
% 0.35/0.61          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.61  thf('9', plain,
% 0.35/0.61      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.61        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.61  thf('10', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.35/0.61          | (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['6', '9'])).
% 0.35/0.61  thf(t69_enumset1, axiom,
% 0.35/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.61  thf('11', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.35/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.61  thf(t70_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.35/0.61  thf('12', plain,
% 0.35/0.61      (![X2 : $i, X3 : $i]:
% 0.35/0.61         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.35/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.61  thf(t71_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.35/0.61  thf('13', plain,
% 0.35/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.61         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.35/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.35/0.61  thf(t72_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.35/0.61  thf('14', plain,
% 0.35/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.61         ((k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10)
% 0.35/0.61           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.35/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.35/0.61  thf(d3_enumset1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.61     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.35/0.61       ( ![G:$i]:
% 0.35/0.61         ( ( r2_hidden @ G @ F ) <=>
% 0.35/0.61           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.35/0.61                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.35/0.61  thf(zf_stmt_7, axiom,
% 0.35/0.61    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.35/0.61     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.35/0.61       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.35/0.61         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_8, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.61     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.35/0.61       ( ![G:$i]:
% 0.35/0.61         ( ( r2_hidden @ G @ F ) <=>
% 0.35/0.61           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.35/0.61  thf('15', plain,
% 0.35/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.35/0.61         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.35/0.61          | (r2_hidden @ X23 @ X29)
% 0.35/0.61          | ((X29) != (k3_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.35/0.61  thf('16', plain,
% 0.35/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.61         ((r2_hidden @ X23 @ (k3_enumset1 @ X28 @ X27 @ X26 @ X25 @ X24))
% 0.35/0.61          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.35/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.35/0.61  thf(t7_ordinal1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.61  thf('17', plain,
% 0.35/0.61      (![X39 : $i, X40 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X39 @ X40) | ~ (r1_tarski @ X40 @ X39))),
% 0.35/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.61  thf('18', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.61         ((zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.35/0.61          | ~ (r1_tarski @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5))),
% 0.35/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.61  thf('19', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.61         (~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.35/0.61          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.35/0.61      inference('sup-', [status(thm)], ['14', '18'])).
% 0.35/0.61  thf('20', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.61         (~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.35/0.61          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2))),
% 0.35/0.61      inference('sup-', [status(thm)], ['13', '19'])).
% 0.35/0.61  thf('21', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.61         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.35/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['12', '20'])).
% 0.35/0.61  thf('22', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.35/0.61          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['11', '21'])).
% 0.35/0.61  thf('23', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.61          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['10', '22'])).
% 0.35/0.61  thf('24', plain,
% 0.35/0.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.61         (((X17) != (X16))
% 0.35/0.61          | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 @ X16))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.35/0.61  thf('25', plain,
% 0.35/0.61      (![X16 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.61         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X20 @ X21 @ X16)),
% 0.35/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.35/0.61  thf('26', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.35/0.61      inference('sup-', [status(thm)], ['23', '25'])).
% 0.35/0.61  thf('27', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_D @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.61  thf('28', plain,
% 0.35/0.61      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.35/0.61         (((k1_relset_1 @ X45 @ X46 @ X44) = (k1_relat_1 @ X44))
% 0.35/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.35/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.61  thf('29', plain,
% 0.35/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.35/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.61  thf('30', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.61      inference('demod', [status(thm)], ['3', '26', '29'])).
% 0.35/0.61  thf(d4_funct_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.61       ( ![B:$i,C:$i]:
% 0.35/0.61         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.61             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.61               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.61           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.35/0.61             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.61               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.35/0.61  thf('31', plain,
% 0.35/0.61      (![X35 : $i, X36 : $i, X38 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X36))
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X35 @ X38) @ X36)
% 0.35/0.61          | ((X38) != (k1_funct_1 @ X36 @ X35))
% 0.35/0.61          | ~ (v1_funct_1 @ X36)
% 0.35/0.61          | ~ (v1_relat_1 @ X36))),
% 0.35/0.61      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.35/0.61  thf('32', plain,
% 0.35/0.61      (![X35 : $i, X36 : $i]:
% 0.35/0.61         (~ (v1_relat_1 @ X36)
% 0.35/0.61          | ~ (v1_funct_1 @ X36)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X35 @ (k1_funct_1 @ X36 @ X35)) @ X36)
% 0.35/0.61          | ~ (r2_hidden @ X35 @ (k1_relat_1 @ X36)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D)
% 0.35/0.61          | ~ (v1_funct_1 @ sk_D)
% 0.35/0.61          | ~ (v1_relat_1 @ sk_D))),
% 0.35/0.61      inference('sup-', [status(thm)], ['30', '32'])).
% 0.35/0.61  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('35', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_D @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(cc1_relset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.61       ( v1_relat_1 @ C ) ))).
% 0.35/0.61  thf('36', plain,
% 0.35/0.61      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.35/0.61         ((v1_relat_1 @ X41)
% 0.35/0.61          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.35/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.61  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.61  thf('38', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.61          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D))),
% 0.35/0.61      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.35/0.61  thf('39', plain,
% 0.35/0.61      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ sk_D)),
% 0.35/0.61      inference('sup-', [status(thm)], ['0', '38'])).
% 0.35/0.61  thf('40', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_D @ 
% 0.35/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(l3_subset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.35/0.61  thf('41', plain,
% 0.35/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X32 @ X33)
% 0.35/0.61          | (r2_hidden @ X32 @ X34)
% 0.35/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.35/0.61      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.35/0.61  thf('42', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.35/0.61          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.35/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.61  thf('43', plain,
% 0.35/0.61      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ 
% 0.35/0.61        (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['39', '42'])).
% 0.35/0.61  thf(t129_zfmisc_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.61     ( ( r2_hidden @
% 0.35/0.61         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.35/0.61       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.35/0.61  thf('44', plain,
% 0.35/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.61         (((X13) = (X14))
% 0.35/0.61          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 0.35/0.61               (k2_zfmisc_1 @ X12 @ (k1_tarski @ X14))))),
% 0.35/0.61      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.35/0.61  thf('45', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.61  thf('46', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('47', plain, ($false),
% 0.35/0.61      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
