%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m4uJbXuP6o

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:18 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 113 expanded)
%              Number of leaves         :   49 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  675 ( 983 expanded)
%              Number of equality atoms :   44 (  58 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v5_relat_1 @ X47 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X53: $i,X54: $i] :
      ( ( zip_tseitin_0 @ X53 @ X54 )
      | ( X53 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( zip_tseitin_0 @ X58 @ X59 )
      | ( zip_tseitin_1 @ X60 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_2 @ X57 @ X55 @ X56 )
      | ( X55
        = ( k1_relset_1 @ X55 @ X56 @ X57 ) )
      | ~ ( zip_tseitin_1 @ X57 @ X56 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k1_relset_1 @ X51 @ X52 @ X50 )
        = ( k1_relat_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k5_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k6_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(fc7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) )).

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc7_subset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ~ ( v1_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( v1_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k1_relat_1 @ X42 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X42 @ X41 ) @ X43 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v5_relat_1 @ X42 @ X43 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','41'])).

thf('43',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','42'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m4uJbXuP6o
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:34:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 81 iterations in 0.103s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.39/0.57                                           $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(t65_funct_2, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.39/0.57       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.39/0.57            ( m1_subset_1 @
% 0.39/0.57              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.39/0.57          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.39/0.57  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.39/0.57         ((v5_relat_1 @ X47 @ X49)
% 0.39/0.57          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.57  thf('3', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(d1_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_1, axiom,
% 0.39/0.57    (![B:$i,A:$i]:
% 0.39/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X53 : $i, X54 : $i]:
% 0.39/0.57         ((zip_tseitin_0 @ X53 @ X54) | ((X53) = (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.57  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_3, axiom,
% 0.39/0.57    (![C:$i,B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_5, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.39/0.57         (~ (zip_tseitin_0 @ X58 @ X59)
% 0.39/0.57          | (zip_tseitin_1 @ X60 @ X58 @ X59)
% 0.39/0.57          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.39/0.57        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.39/0.57        | (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.39/0.57  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.39/0.57         (~ (v1_funct_2 @ X57 @ X55 @ X56)
% 0.39/0.57          | ((X55) = (k1_relset_1 @ X55 @ X56 @ X57))
% 0.39/0.57          | ~ (zip_tseitin_1 @ X57 @ X56 @ X55))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      ((~ (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.39/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.39/0.57         (((k1_relset_1 @ X51 @ X52 @ X50) = (k1_relat_1 @ X50))
% 0.39/0.57          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      ((~ (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.39/0.57        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.39/0.57      inference('demod', [status(thm)], ['13', '16'])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k1_tarski @ sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['10', '17'])).
% 0.39/0.57  thf(t69_enumset1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.57  thf('19', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.57  thf(t70_enumset1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.57  thf(t71_enumset1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.57         ((k2_enumset1 @ X8 @ X8 @ X9 @ X10) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.57  thf(t72_enumset1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         ((k3_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14)
% 0.39/0.57           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.39/0.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.39/0.57  thf(t73_enumset1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.57     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.39/0.57       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         ((k4_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.39/0.57           = (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.39/0.57  thf(t74_enumset1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.57     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.39/0.57       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.57         ((k5_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.39/0.57           = (k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.39/0.57  thf(t75_enumset1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.39/0.57     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.39/0.57       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.57         ((k6_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.39/0.57           = (k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32))),
% 0.39/0.57      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.39/0.57  thf(fc7_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.39/0.57     ( ~( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.39/0.57         X40 : $i]:
% 0.39/0.57         ~ (v1_xboole_0 @ 
% 0.39/0.57            (k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc7_subset_1])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.57         ~ (v1_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         ~ (v1_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         ~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['23', '28'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['21', '30'])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '31'])).
% 0.39/0.57  thf('33', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['19', '32'])).
% 0.39/0.57  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '33'])).
% 0.39/0.57  thf(t172_funct_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57       ( ![C:$i]:
% 0.39/0.57         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.57           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X41 @ (k1_relat_1 @ X42))
% 0.39/0.57          | (r2_hidden @ (k1_funct_1 @ X42 @ X41) @ X43)
% 0.39/0.57          | ~ (v1_funct_1 @ X42)
% 0.39/0.57          | ~ (v5_relat_1 @ X42 @ X43)
% 0.39/0.57          | ~ (v1_relat_1 @ X42))),
% 0.39/0.57      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.39/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.39/0.57          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.57          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc1_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( v1_relat_1 @ C ) ))).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.39/0.57         ((v1_relat_1 @ X44)
% 0.39/0.57          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.57  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.57  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.39/0.57          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.39/0.57          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['36', '39', '40'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.39/0.57          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '41'])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '42'])).
% 0.39/0.57  thf(d1_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (![X0 : $i, X3 : $i]:
% 0.39/0.57         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['44'])).
% 0.39/0.57  thf('46', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['43', '45'])).
% 0.39/0.57  thf('47', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('48', plain, ($false),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
