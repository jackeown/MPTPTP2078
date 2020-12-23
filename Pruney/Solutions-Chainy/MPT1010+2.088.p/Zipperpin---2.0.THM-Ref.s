%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1TAdFRSMmz

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:25 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 213 expanded)
%              Number of leaves         :   57 (  88 expanded)
%              Depth                    :   19
%              Number of atoms          :  953 (1982 expanded)
%              Number of equality atoms :   60 ( 117 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X5 )
      | ( X2 = X3 )
      | ( X2 = X4 )
      | ( X2 = X5 ) ) ),
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
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    r2_hidden @ sk_C @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_2 @ B @ A ) ) )).

thf('3',plain,(
    ! [X56: $i,X57: $i] :
      ( ( zip_tseitin_2 @ X56 @ X57 )
      | ( X56 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_2 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_3,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_2 @ B @ A )
         => ( zip_tseitin_3 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( zip_tseitin_2 @ X61 @ X62 )
      | ( zip_tseitin_3 @ X63 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('8',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_2 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( zip_tseitin_3 @ sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v1_funct_2 @ X60 @ X58 @ X59 )
      | ( X58
        = ( k1_relset_1 @ X58 @ X59 @ X60 ) )
      | ~ ( zip_tseitin_3 @ X60 @ X59 @ X58 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('12',plain,
    ( ~ ( zip_tseitin_3 @ sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k1_relset_1 @ X54 @ X55 @ X53 )
        = ( k1_relat_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( zip_tseitin_3 @ sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ X6 @ X10 )
      | ( X10
       != ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k1_enumset1 @ X9 @ X8 @ X7 ) )
      | ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r1_tarski @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ~ ( zip_tseitin_0 @ X1 @ X3 @ X4 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_9,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X36 @ X37 @ X38 @ X39 )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X39 ) )
      | ~ ( r2_hidden @ X36 @ X38 )
      | ( X37
       != ( k1_funct_1 @ X39 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('31',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X36 @ X38 )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X39 ) )
      | ( zip_tseitin_1 @ X36 @ ( k1_funct_1 @ X39 @ X36 ) @ X38 @ X39 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_C @ X0 )
      | ( zip_tseitin_1 @ sk_C @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','32'])).

thf('34',plain,(
    zip_tseitin_1 @ sk_C @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ sk_A @ sk_D_1 ),
    inference('sup-',[status(thm)],['1','33'])).

thf(zf_stmt_10,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_1 @ E @ D @ B @ A ) ) ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i,X44: $i,X46: $i,X47: $i] :
      ( ( X44
       != ( k9_relat_1 @ X42 @ X41 ) )
      | ( r2_hidden @ X46 @ X44 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('36',plain,(
    ! [X41: $i,X42: $i,X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X41 @ X42 )
      | ( r2_hidden @ X46 @ ( k9_relat_1 @ X42 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X34: $i] :
      ( ( ( k9_relat_1 @ X34 @ ( k1_relat_1 @ X34 ) )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('40',plain,
    ( ( ( k9_relat_1 @ sk_D_1 @ sk_A )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X32: $i,X33: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_A )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('49',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['37','46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( v5_relat_1 @ X50 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v5_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('53',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v5_relat_1 @ X30 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('56',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('64',plain,(
    ! [X19: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('65',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X7 @ X8 @ X9 )
      | ( X10
       != ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('69',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X7 @ X8 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','72'])).

thf('74',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C )
    = sk_B ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1TAdFRSMmz
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 386 iterations in 0.457s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.75/0.94  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.94  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.75/0.94  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 0.75/0.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.75/0.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.94  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.75/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.94  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.94  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.94  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.94  thf(d1_enumset1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.94       ( ![E:$i]:
% 0.75/0.94         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.94           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, axiom,
% 0.75/0.94    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.94     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.94       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.94  thf('0', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X2 @ X3 @ X4 @ X5)
% 0.75/0.94          | ((X2) = (X3))
% 0.75/0.94          | ((X2) = (X4))
% 0.75/0.94          | ((X2) = (X5)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t65_funct_2, conjecture,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.75/0.94         ( m1_subset_1 @
% 0.75/0.94           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.75/0.94       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_1, negated_conjecture,
% 0.75/0.94    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.75/0.94            ( m1_subset_1 @
% 0.75/0.94              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.75/0.94          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.75/0.94  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('2', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf(d1_funct_2, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.94           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.94             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.94         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.94           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.94             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_2, axiom,
% 0.75/0.94    (![B:$i,A:$i]:
% 0.75/0.94     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.94       ( zip_tseitin_2 @ B @ A ) ))).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (![X56 : $i, X57 : $i]:
% 0.75/0.94         ((zip_tseitin_2 @ X56 @ X57) | ((X56) = (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.94  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.94  thf('4', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.94  thf('5', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((r1_tarski @ X0 @ X1) | (zip_tseitin_2 @ X0 @ X2))),
% 0.75/0.94      inference('sup+', [status(thm)], ['3', '4'])).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D_1 @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf(zf_stmt_3, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.75/0.94  thf(zf_stmt_4, axiom,
% 0.75/0.94    (![C:$i,B:$i,A:$i]:
% 0.75/0.94     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 0.75/0.94       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $o).
% 0.75/0.94  thf(zf_stmt_6, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( ( zip_tseitin_2 @ B @ A ) => ( zip_tseitin_3 @ C @ B @ A ) ) & 
% 0.75/0.94         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.94           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.94             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.75/0.94         (~ (zip_tseitin_2 @ X61 @ X62)
% 0.75/0.94          | (zip_tseitin_3 @ X63 @ X61 @ X62)
% 0.75/0.94          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      (((zip_tseitin_3 @ sk_D_1 @ (k1_tarski @ sk_B) @ sk_A)
% 0.75/0.94        | ~ (zip_tseitin_2 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | (zip_tseitin_3 @ sk_D_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['5', '8'])).
% 0.75/0.94  thf('10', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.75/0.94         (~ (v1_funct_2 @ X60 @ X58 @ X59)
% 0.75/0.94          | ((X58) = (k1_relset_1 @ X58 @ X59 @ X60))
% 0.75/0.94          | ~ (zip_tseitin_3 @ X60 @ X59 @ X58))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      ((~ (zip_tseitin_3 @ sk_D_1 @ (k1_tarski @ sk_B) @ sk_A)
% 0.75/0.94        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D_1 @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.75/0.94         (((k1_relset_1 @ X54 @ X55 @ X53) = (k1_relat_1 @ X53))
% 0.75/0.94          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55))))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_1)
% 0.75/0.94         = (k1_relat_1 @ sk_D_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      ((~ (zip_tseitin_3 @ sk_D_1 @ (k1_tarski @ sk_B) @ sk_A)
% 0.75/0.94        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['12', '15'])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['9', '16'])).
% 0.75/0.94  thf(t69_enumset1, axiom,
% 0.75/0.94    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.94  thf('18', plain,
% 0.75/0.94      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.75/0.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.94  thf(t70_enumset1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (![X14 : $i, X15 : $i]:
% 0.75/0.94         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.94  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.94  thf(zf_stmt_8, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.94       ( ![E:$i]:
% 0.75/0.94         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.75/0.94          | (r2_hidden @ X6 @ X10)
% 0.75/0.94          | ((X10) != (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.94         ((r2_hidden @ X6 @ (k1_enumset1 @ X9 @ X8 @ X7))
% 0.75/0.94          | (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9))),
% 0.75/0.94      inference('simplify', [status(thm)], ['20'])).
% 0.75/0.94  thf(t7_ordinal1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      (![X48 : $i, X49 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X48 @ X49) | ~ (r1_tarski @ X49 @ X48))),
% 0.75/0.94      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.75/0.94          | ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3))),
% 0.75/0.94      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.75/0.94          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['19', '23'])).
% 0.75/0.94  thf('25', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.75/0.94          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['18', '24'])).
% 0.75/0.94  thf('26', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (((sk_A) = (k1_relat_1 @ sk_D_1))
% 0.75/0.94          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['17', '25'])).
% 0.75/0.94  thf('27', plain,
% 0.75/0.94      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.94         (((X2) != (X1)) | ~ (zip_tseitin_0 @ X2 @ X3 @ X4 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X1 : $i, X3 : $i, X4 : $i]: ~ (zip_tseitin_0 @ X1 @ X3 @ X4 @ X1)),
% 0.75/0.94      inference('simplify', [status(thm)], ['27'])).
% 0.75/0.94  thf('29', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['26', '28'])).
% 0.75/0.94  thf(d12_funct_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.75/0.94       ( ![B:$i,C:$i]:
% 0.75/0.94         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.75/0.94           ( ![D:$i]:
% 0.75/0.94             ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.94               ( ?[E:$i]:
% 0.75/0.94                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.75/0.94                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_9, axiom,
% 0.75/0.94    (![E:$i,D:$i,B:$i,A:$i]:
% 0.75/0.94     ( ( zip_tseitin_1 @ E @ D @ B @ A ) <=>
% 0.75/0.94       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.75/0.94         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.75/0.94         ((zip_tseitin_1 @ X36 @ X37 @ X38 @ X39)
% 0.75/0.94          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ X39))
% 0.75/0.94          | ~ (r2_hidden @ X36 @ X38)
% 0.75/0.94          | ((X37) != (k1_funct_1 @ X39 @ X36)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X36 @ X38)
% 0.75/0.94          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ X39))
% 0.75/0.94          | (zip_tseitin_1 @ X36 @ (k1_funct_1 @ X39 @ X36) @ X38 @ X39))),
% 0.75/0.94      inference('simplify', [status(thm)], ['30'])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X0 @ sk_A)
% 0.75/0.94          | (zip_tseitin_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1 @ sk_D_1)
% 0.75/0.94          | ~ (r2_hidden @ X0 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['29', '31'])).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (r2_hidden @ sk_C @ X0)
% 0.75/0.94          | (zip_tseitin_1 @ sk_C @ (k1_funct_1 @ sk_D_1 @ sk_C) @ X0 @ sk_D_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['2', '32'])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      ((zip_tseitin_1 @ sk_C @ (k1_funct_1 @ sk_D_1 @ sk_C) @ sk_A @ sk_D_1)),
% 0.75/0.94      inference('sup-', [status(thm)], ['1', '33'])).
% 0.75/0.94  thf(zf_stmt_10, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.75/0.94  thf(zf_stmt_11, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.94       ( ![B:$i,C:$i]:
% 0.75/0.94         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.75/0.94           ( ![D:$i]:
% 0.75/0.94             ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.94               ( ?[E:$i]: ( zip_tseitin_1 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X41 : $i, X42 : $i, X44 : $i, X46 : $i, X47 : $i]:
% 0.75/0.94         (((X44) != (k9_relat_1 @ X42 @ X41))
% 0.75/0.94          | (r2_hidden @ X46 @ X44)
% 0.75/0.94          | ~ (zip_tseitin_1 @ X47 @ X46 @ X41 @ X42)
% 0.75/0.94          | ~ (v1_funct_1 @ X42)
% 0.75/0.94          | ~ (v1_relat_1 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_11])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      (![X41 : $i, X42 : $i, X46 : $i, X47 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ X42)
% 0.75/0.94          | ~ (v1_funct_1 @ X42)
% 0.75/0.94          | ~ (zip_tseitin_1 @ X47 @ X46 @ X41 @ X42)
% 0.75/0.94          | (r2_hidden @ X46 @ (k9_relat_1 @ X42 @ X41)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['35'])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ 
% 0.75/0.94         (k9_relat_1 @ sk_D_1 @ sk_A))
% 0.75/0.94        | ~ (v1_funct_1 @ sk_D_1)
% 0.75/0.94        | ~ (v1_relat_1 @ sk_D_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['34', '36'])).
% 0.75/0.94  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['26', '28'])).
% 0.75/0.94  thf(t146_relat_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ A ) =>
% 0.75/0.94       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (![X34 : $i]:
% 0.75/0.94         (((k9_relat_1 @ X34 @ (k1_relat_1 @ X34)) = (k2_relat_1 @ X34))
% 0.75/0.94          | ~ (v1_relat_1 @ X34))),
% 0.75/0.94      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      ((((k9_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))
% 0.75/0.94        | ~ (v1_relat_1 @ sk_D_1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['38', '39'])).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D_1 @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf(cc2_relat_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ A ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X28 : $i, X29 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.75/0.94          | (v1_relat_1 @ X28)
% 0.75/0.94          | ~ (v1_relat_1 @ X29))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.94        | (v1_relat_1 @ sk_D_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['41', '42'])).
% 0.75/0.94  thf(fc6_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (![X32 : $i, X33 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X32 @ X33))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.75/0.94  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.94  thf('46', plain, (((k9_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))),
% 0.75/0.94      inference('demod', [status(thm)], ['40', '45'])).
% 0.75/0.94  thf('47', plain, ((v1_funct_1 @ sk_D_1)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))),
% 0.75/0.94      inference('demod', [status(thm)], ['37', '46', '47', '48'])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D_1 @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf(cc2_relset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.75/0.94         ((v5_relat_1 @ X50 @ X52)
% 0.75/0.94          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.94  thf('52', plain, ((v5_relat_1 @ sk_D_1 @ (k1_tarski @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/0.94  thf(d19_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ B ) =>
% 0.75/0.94       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X30 : $i, X31 : $i]:
% 0.75/0.94         (~ (v5_relat_1 @ X30 @ X31)
% 0.75/0.94          | (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.75/0.94          | ~ (v1_relat_1 @ X30))),
% 0.75/0.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ sk_D_1)
% 0.75/0.94        | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ (k1_tarski @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['52', '53'])).
% 0.75/0.94  thf('55', plain, ((v1_relat_1 @ sk_D_1)),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.94  thf('56', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ (k1_tarski @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['54', '55'])).
% 0.75/0.94  thf(t3_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X22 : $i, X24 : $i]:
% 0.75/0.94         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.94  thf(t4_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.75/0.94       ( m1_subset_1 @ A @ C ) ))).
% 0.75/0.94  thf('59', plain,
% 0.75/0.94      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X25 @ X26)
% 0.75/0.94          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.75/0.94          | (m1_subset_1 @ X25 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [t4_subset])).
% 0.75/0.94  thf('60', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B))
% 0.75/0.94          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('61', plain,
% 0.75/0.94      ((m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k1_tarski @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['49', '60'])).
% 0.75/0.94  thf(t2_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ A @ B ) =>
% 0.75/0.94       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.75/0.94  thf('62', plain,
% 0.75/0.94      (![X20 : $i, X21 : $i]:
% 0.75/0.94         ((r2_hidden @ X20 @ X21)
% 0.75/0.94          | (v1_xboole_0 @ X21)
% 0.75/0.94          | ~ (m1_subset_1 @ X20 @ X21))),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_subset])).
% 0.75/0.94  thf('63', plain,
% 0.75/0.94      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.75/0.94        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k1_tarski @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['61', '62'])).
% 0.75/0.94  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.75/0.94  thf('64', plain, (![X19 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X19))),
% 0.75/0.94      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.75/0.94  thf('65', plain,
% 0.75/0.94      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k1_tarski @ sk_B))),
% 0.75/0.94      inference('clc', [status(thm)], ['63', '64'])).
% 0.75/0.94  thf('66', plain,
% 0.75/0.94      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.75/0.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.94  thf('67', plain,
% 0.75/0.94      (![X14 : $i, X15 : $i]:
% 0.75/0.94         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.75/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.94  thf('68', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X11 @ X10)
% 0.75/0.94          | ~ (zip_tseitin_0 @ X11 @ X7 @ X8 @ X9)
% 0.75/0.94          | ((X10) != (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.75/0.94  thf('69', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.75/0.94         (~ (zip_tseitin_0 @ X11 @ X7 @ X8 @ X9)
% 0.75/0.94          | ~ (r2_hidden @ X11 @ (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['68'])).
% 0.75/0.94  thf('70', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.94          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['67', '69'])).
% 0.75/0.94  thf('71', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.94          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['66', '70'])).
% 0.75/0.94  thf('72', plain,
% 0.75/0.94      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D_1 @ sk_C) @ sk_B @ sk_B @ sk_B)),
% 0.75/0.94      inference('sup-', [status(thm)], ['65', '71'])).
% 0.75/0.94  thf('73', plain,
% 0.75/0.94      ((((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B))
% 0.75/0.94        | ((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B))
% 0.75/0.94        | ((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['0', '72'])).
% 0.75/0.94  thf('74', plain, (((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B))),
% 0.75/0.94      inference('simplify', [status(thm)], ['73'])).
% 0.75/0.94  thf('75', plain, (((k1_funct_1 @ sk_D_1 @ sk_C) != (sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('76', plain, ($false),
% 0.75/0.94      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
