%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qJyue9aq5X

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:32 EST 2020

% Result     : Theorem 24.56s
% Output     : Refutation 24.56s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 597 expanded)
%              Number of leaves         :   41 ( 199 expanded)
%              Depth                    :   25
%              Number of atoms          : 1061 (6711 expanded)
%              Number of equality atoms :   74 ( 327 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ( X48
        = ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ~ ( zip_tseitin_1 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X40 @ X41 @ X39 )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('34',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( r2_relset_1 @ X43 @ X44 @ X42 @ X45 )
      | ( X42 != X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_relset_1 @ X43 @ X44 @ X45 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','37'])).

thf('39',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['41','56'])).

thf('58',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','57'])).

thf('59',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ( X48
        = ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ~ ( zip_tseitin_1 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X40 @ X41 @ X39 )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['41','56'])).

thf('71',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['66','71'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('73',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( X27 = X26 )
      | ( r2_hidden @ ( sk_C_1 @ X26 @ X27 ) @ ( k1_relat_1 @ X27 ) )
      | ( ( k1_relat_1 @ X27 )
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('76',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','77','78','79'])).

thf('81',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['81','84','85'])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['86'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('89',plain,
    ( ( sk_C_2 = sk_D )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X54: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X54 )
        = ( k1_funct_1 @ sk_D @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( X27 = X26 )
      | ( ( k1_funct_1 @ X27 @ ( sk_C_1 @ X26 @ X27 ) )
       != ( k1_funct_1 @ X26 @ ( sk_C_1 @ X26 @ X27 ) ) )
      | ( ( k1_relat_1 @ X27 )
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('94',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('96',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','58'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['82','83'])).

thf('101',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100'])).

thf('102',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_relset_1 @ X43 @ X44 @ X45 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('105',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qJyue9aq5X
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:21:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 24.56/24.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 24.56/24.83  % Solved by: fo/fo7.sh
% 24.56/24.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.56/24.83  % done 10896 iterations in 24.360s
% 24.56/24.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 24.56/24.83  % SZS output start Refutation
% 24.56/24.83  thf(sk_A_type, type, sk_A: $i).
% 24.56/24.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 24.56/24.83  thf(sk_C_2_type, type, sk_C_2: $i).
% 24.56/24.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 24.56/24.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.56/24.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 24.56/24.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 24.56/24.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 24.56/24.83  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 24.56/24.83  thf(sk_D_type, type, sk_D: $i).
% 24.56/24.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 24.56/24.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 24.56/24.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 24.56/24.83  thf(sk_B_type, type, sk_B: $i > $i).
% 24.56/24.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 24.56/24.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 24.56/24.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 24.56/24.83  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 24.56/24.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 24.56/24.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 24.56/24.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 24.56/24.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 24.56/24.83  thf(t113_funct_2, conjecture,
% 24.56/24.83    (![A:$i,B:$i,C:$i]:
% 24.56/24.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 24.56/24.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 24.56/24.83       ( ![D:$i]:
% 24.56/24.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 24.56/24.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 24.56/24.83           ( ( ![E:$i]:
% 24.56/24.83               ( ( m1_subset_1 @ E @ A ) =>
% 24.56/24.83                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 24.56/24.83             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 24.56/24.83  thf(zf_stmt_0, negated_conjecture,
% 24.56/24.83    (~( ![A:$i,B:$i,C:$i]:
% 24.56/24.83        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 24.56/24.83            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 24.56/24.83          ( ![D:$i]:
% 24.56/24.83            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 24.56/24.83                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 24.56/24.83              ( ( ![E:$i]:
% 24.56/24.83                  ( ( m1_subset_1 @ E @ A ) =>
% 24.56/24.83                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 24.56/24.83                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 24.56/24.83    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 24.56/24.83  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf(d1_funct_2, axiom,
% 24.56/24.83    (![A:$i,B:$i,C:$i]:
% 24.56/24.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.56/24.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 24.56/24.83           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 24.56/24.83             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 24.56/24.83         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 24.56/24.83           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 24.56/24.83             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 24.56/24.83  thf(zf_stmt_1, axiom,
% 24.56/24.83    (![C:$i,B:$i,A:$i]:
% 24.56/24.83     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 24.56/24.83       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 24.56/24.83  thf('2', plain,
% 24.56/24.83      (![X48 : $i, X49 : $i, X50 : $i]:
% 24.56/24.83         (~ (v1_funct_2 @ X50 @ X48 @ X49)
% 24.56/24.83          | ((X48) = (k1_relset_1 @ X48 @ X49 @ X50))
% 24.56/24.83          | ~ (zip_tseitin_1 @ X50 @ X49 @ X48))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 24.56/24.83  thf('3', plain,
% 24.56/24.83      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 24.56/24.83        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 24.56/24.83      inference('sup-', [status(thm)], ['1', '2'])).
% 24.56/24.83  thf('4', plain,
% 24.56/24.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf(redefinition_k1_relset_1, axiom,
% 24.56/24.83    (![A:$i,B:$i,C:$i]:
% 24.56/24.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.56/24.83       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 24.56/24.83  thf('5', plain,
% 24.56/24.83      (![X39 : $i, X40 : $i, X41 : $i]:
% 24.56/24.83         (((k1_relset_1 @ X40 @ X41 @ X39) = (k1_relat_1 @ X39))
% 24.56/24.83          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 24.56/24.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 24.56/24.83  thf('6', plain,
% 24.56/24.83      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 24.56/24.83      inference('sup-', [status(thm)], ['4', '5'])).
% 24.56/24.83  thf('7', plain,
% 24.56/24.83      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 24.56/24.83        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 24.56/24.83      inference('demod', [status(thm)], ['3', '6'])).
% 24.56/24.83  thf('8', plain,
% 24.56/24.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 24.56/24.83  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 24.56/24.83  thf(zf_stmt_4, axiom,
% 24.56/24.83    (![B:$i,A:$i]:
% 24.56/24.83     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 24.56/24.83       ( zip_tseitin_0 @ B @ A ) ))).
% 24.56/24.83  thf(zf_stmt_5, axiom,
% 24.56/24.83    (![A:$i,B:$i,C:$i]:
% 24.56/24.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.56/24.83       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 24.56/24.83         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 24.56/24.83           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 24.56/24.83             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 24.56/24.83  thf('9', plain,
% 24.56/24.83      (![X51 : $i, X52 : $i, X53 : $i]:
% 24.56/24.83         (~ (zip_tseitin_0 @ X51 @ X52)
% 24.56/24.83          | (zip_tseitin_1 @ X53 @ X51 @ X52)
% 24.56/24.83          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 24.56/24.83  thf('10', plain,
% 24.56/24.83      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 24.56/24.83        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 24.56/24.83      inference('sup-', [status(thm)], ['8', '9'])).
% 24.56/24.83  thf('11', plain,
% 24.56/24.83      (![X46 : $i, X47 : $i]:
% 24.56/24.83         ((zip_tseitin_0 @ X46 @ X47) | ((X46) = (k1_xboole_0)))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 24.56/24.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 24.56/24.83  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 24.56/24.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 24.56/24.83  thf('13', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 24.56/24.83      inference('sup+', [status(thm)], ['11', '12'])).
% 24.56/24.83  thf(l13_xboole_0, axiom,
% 24.56/24.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 24.56/24.83  thf('14', plain,
% 24.56/24.83      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 24.56/24.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 24.56/24.83  thf(t113_zfmisc_1, axiom,
% 24.56/24.83    (![A:$i,B:$i]:
% 24.56/24.83     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 24.56/24.83       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 24.56/24.83  thf('15', plain,
% 24.56/24.83      (![X12 : $i, X13 : $i]:
% 24.56/24.83         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 24.56/24.83          | ((X13) != (k1_xboole_0)))),
% 24.56/24.83      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 24.56/24.83  thf('16', plain,
% 24.56/24.83      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 24.56/24.83      inference('simplify', [status(thm)], ['15'])).
% 24.56/24.83  thf('17', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i]:
% 24.56/24.83         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 24.56/24.83      inference('sup+', [status(thm)], ['14', '16'])).
% 24.56/24.83  thf(d1_xboole_0, axiom,
% 24.56/24.83    (![A:$i]:
% 24.56/24.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 24.56/24.83  thf('18', plain,
% 24.56/24.83      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 24.56/24.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 24.56/24.83  thf('19', plain,
% 24.56/24.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf(t3_subset, axiom,
% 24.56/24.83    (![A:$i,B:$i]:
% 24.56/24.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 24.56/24.83  thf('20', plain,
% 24.56/24.83      (![X17 : $i, X18 : $i]:
% 24.56/24.83         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 24.56/24.83      inference('cnf', [status(esa)], [t3_subset])).
% 24.56/24.83  thf('21', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 24.56/24.83      inference('sup-', [status(thm)], ['19', '20'])).
% 24.56/24.83  thf(d3_tarski, axiom,
% 24.56/24.83    (![A:$i,B:$i]:
% 24.56/24.83     ( ( r1_tarski @ A @ B ) <=>
% 24.56/24.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 24.56/24.83  thf('22', plain,
% 24.56/24.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 24.56/24.83         (~ (r2_hidden @ X3 @ X4)
% 24.56/24.83          | (r2_hidden @ X3 @ X5)
% 24.56/24.83          | ~ (r1_tarski @ X4 @ X5))),
% 24.56/24.83      inference('cnf', [status(esa)], [d3_tarski])).
% 24.56/24.83  thf('23', plain,
% 24.56/24.83      (![X0 : $i]:
% 24.56/24.83         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 24.56/24.83          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 24.56/24.83      inference('sup-', [status(thm)], ['21', '22'])).
% 24.56/24.83  thf('24', plain,
% 24.56/24.83      (((v1_xboole_0 @ sk_C_2)
% 24.56/24.83        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('sup-', [status(thm)], ['18', '23'])).
% 24.56/24.83  thf('25', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 24.56/24.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 24.56/24.83  thf('26', plain,
% 24.56/24.83      (((v1_xboole_0 @ sk_C_2)
% 24.56/24.83        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('sup-', [status(thm)], ['24', '25'])).
% 24.56/24.83  thf('27', plain,
% 24.56/24.83      ((~ (v1_xboole_0 @ k1_xboole_0)
% 24.56/24.83        | ~ (v1_xboole_0 @ sk_B_1)
% 24.56/24.83        | (v1_xboole_0 @ sk_C_2))),
% 24.56/24.83      inference('sup-', [status(thm)], ['17', '26'])).
% 24.56/24.83  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 24.56/24.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 24.56/24.83  thf('29', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_2))),
% 24.56/24.83      inference('demod', [status(thm)], ['27', '28'])).
% 24.56/24.83  thf('30', plain,
% 24.56/24.83      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 24.56/24.83      inference('sup-', [status(thm)], ['13', '29'])).
% 24.56/24.83  thf('31', plain,
% 24.56/24.83      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 24.56/24.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 24.56/24.83  thf('32', plain,
% 24.56/24.83      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 24.56/24.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 24.56/24.83  thf(t4_subset_1, axiom,
% 24.56/24.83    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 24.56/24.83  thf('33', plain,
% 24.56/24.83      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 24.56/24.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 24.56/24.83  thf(redefinition_r2_relset_1, axiom,
% 24.56/24.83    (![A:$i,B:$i,C:$i,D:$i]:
% 24.56/24.83     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 24.56/24.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 24.56/24.83       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 24.56/24.83  thf('34', plain,
% 24.56/24.83      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 24.56/24.83         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 24.56/24.83          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 24.56/24.83          | (r2_relset_1 @ X43 @ X44 @ X42 @ X45)
% 24.56/24.83          | ((X42) != (X45)))),
% 24.56/24.83      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 24.56/24.83  thf('35', plain,
% 24.56/24.83      (![X43 : $i, X44 : $i, X45 : $i]:
% 24.56/24.83         ((r2_relset_1 @ X43 @ X44 @ X45 @ X45)
% 24.56/24.83          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 24.56/24.83      inference('simplify', [status(thm)], ['34'])).
% 24.56/24.83  thf('36', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 24.56/24.83      inference('sup-', [status(thm)], ['33', '35'])).
% 24.56/24.83  thf('37', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.56/24.83         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 24.56/24.83      inference('sup+', [status(thm)], ['32', '36'])).
% 24.56/24.83  thf('38', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.56/24.83         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 24.56/24.83          | ~ (v1_xboole_0 @ X0)
% 24.56/24.83          | ~ (v1_xboole_0 @ X1))),
% 24.56/24.83      inference('sup+', [status(thm)], ['31', '37'])).
% 24.56/24.83  thf('39', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf('40', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 24.56/24.83      inference('sup-', [status(thm)], ['38', '39'])).
% 24.56/24.83  thf('41', plain,
% 24.56/24.83      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 24.56/24.83      inference('sup-', [status(thm)], ['30', '40'])).
% 24.56/24.83  thf('42', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 24.56/24.83      inference('sup+', [status(thm)], ['11', '12'])).
% 24.56/24.83  thf('43', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i]:
% 24.56/24.83         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 24.56/24.83      inference('sup+', [status(thm)], ['14', '16'])).
% 24.56/24.83  thf('44', plain,
% 24.56/24.83      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 24.56/24.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 24.56/24.83  thf('45', plain,
% 24.56/24.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf('46', plain,
% 24.56/24.83      (![X17 : $i, X18 : $i]:
% 24.56/24.83         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 24.56/24.83      inference('cnf', [status(esa)], [t3_subset])).
% 24.56/24.83  thf('47', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 24.56/24.83      inference('sup-', [status(thm)], ['45', '46'])).
% 24.56/24.83  thf('48', plain,
% 24.56/24.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 24.56/24.83         (~ (r2_hidden @ X3 @ X4)
% 24.56/24.83          | (r2_hidden @ X3 @ X5)
% 24.56/24.83          | ~ (r1_tarski @ X4 @ X5))),
% 24.56/24.83      inference('cnf', [status(esa)], [d3_tarski])).
% 24.56/24.83  thf('49', plain,
% 24.56/24.83      (![X0 : $i]:
% 24.56/24.83         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 24.56/24.83          | ~ (r2_hidden @ X0 @ sk_D))),
% 24.56/24.83      inference('sup-', [status(thm)], ['47', '48'])).
% 24.56/24.83  thf('50', plain,
% 24.56/24.83      (((v1_xboole_0 @ sk_D)
% 24.56/24.83        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('sup-', [status(thm)], ['44', '49'])).
% 24.56/24.83  thf('51', plain,
% 24.56/24.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 24.56/24.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 24.56/24.83  thf('52', plain,
% 24.56/24.83      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('sup-', [status(thm)], ['50', '51'])).
% 24.56/24.83  thf('53', plain,
% 24.56/24.83      ((~ (v1_xboole_0 @ k1_xboole_0)
% 24.56/24.83        | ~ (v1_xboole_0 @ sk_B_1)
% 24.56/24.83        | (v1_xboole_0 @ sk_D))),
% 24.56/24.83      inference('sup-', [status(thm)], ['43', '52'])).
% 24.56/24.83  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 24.56/24.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 24.56/24.83  thf('55', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_D))),
% 24.56/24.83      inference('demod', [status(thm)], ['53', '54'])).
% 24.56/24.83  thf('56', plain,
% 24.56/24.83      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 24.56/24.83      inference('sup-', [status(thm)], ['42', '55'])).
% 24.56/24.83  thf('57', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 24.56/24.83      inference('clc', [status(thm)], ['41', '56'])).
% 24.56/24.83  thf('58', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 24.56/24.83      inference('demod', [status(thm)], ['10', '57'])).
% 24.56/24.83  thf('59', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 24.56/24.83      inference('demod', [status(thm)], ['7', '58'])).
% 24.56/24.83  thf('60', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf('61', plain,
% 24.56/24.83      (![X48 : $i, X49 : $i, X50 : $i]:
% 24.56/24.83         (~ (v1_funct_2 @ X50 @ X48 @ X49)
% 24.56/24.83          | ((X48) = (k1_relset_1 @ X48 @ X49 @ X50))
% 24.56/24.83          | ~ (zip_tseitin_1 @ X50 @ X49 @ X48))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 24.56/24.83  thf('62', plain,
% 24.56/24.83      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 24.56/24.83        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 24.56/24.83      inference('sup-', [status(thm)], ['60', '61'])).
% 24.56/24.83  thf('63', plain,
% 24.56/24.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf('64', plain,
% 24.56/24.83      (![X39 : $i, X40 : $i, X41 : $i]:
% 24.56/24.83         (((k1_relset_1 @ X40 @ X41 @ X39) = (k1_relat_1 @ X39))
% 24.56/24.83          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 24.56/24.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 24.56/24.83  thf('65', plain,
% 24.56/24.83      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 24.56/24.83      inference('sup-', [status(thm)], ['63', '64'])).
% 24.56/24.83  thf('66', plain,
% 24.56/24.83      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 24.56/24.83        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 24.56/24.83      inference('demod', [status(thm)], ['62', '65'])).
% 24.56/24.83  thf('67', plain,
% 24.56/24.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.83  thf('68', plain,
% 24.56/24.83      (![X51 : $i, X52 : $i, X53 : $i]:
% 24.56/24.83         (~ (zip_tseitin_0 @ X51 @ X52)
% 24.56/24.83          | (zip_tseitin_1 @ X53 @ X51 @ X52)
% 24.56/24.83          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 24.56/24.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 24.56/24.83  thf('69', plain,
% 24.56/24.83      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 24.56/24.83        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 24.56/24.83      inference('sup-', [status(thm)], ['67', '68'])).
% 24.56/24.83  thf('70', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 24.56/24.83      inference('clc', [status(thm)], ['41', '56'])).
% 24.56/24.83  thf('71', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 24.56/24.83      inference('demod', [status(thm)], ['69', '70'])).
% 24.56/24.83  thf('72', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 24.56/24.83      inference('demod', [status(thm)], ['66', '71'])).
% 24.56/24.83  thf(t9_funct_1, axiom,
% 24.56/24.83    (![A:$i]:
% 24.56/24.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 24.56/24.83       ( ![B:$i]:
% 24.56/24.83         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 24.56/24.83           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 24.56/24.83               ( ![C:$i]:
% 24.56/24.83                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 24.56/24.83                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 24.56/24.83             ( ( A ) = ( B ) ) ) ) ) ))).
% 24.56/24.83  thf('73', plain,
% 24.56/24.83      (![X26 : $i, X27 : $i]:
% 24.56/24.83         (~ (v1_relat_1 @ X26)
% 24.56/24.83          | ~ (v1_funct_1 @ X26)
% 24.56/24.83          | ((X27) = (X26))
% 24.56/24.83          | (r2_hidden @ (sk_C_1 @ X26 @ X27) @ (k1_relat_1 @ X27))
% 24.56/24.83          | ((k1_relat_1 @ X27) != (k1_relat_1 @ X26))
% 24.56/24.84          | ~ (v1_funct_1 @ X27)
% 24.56/24.84          | ~ (v1_relat_1 @ X27))),
% 24.56/24.84      inference('cnf', [status(esa)], [t9_funct_1])).
% 24.56/24.84  thf('74', plain,
% 24.56/24.84      (![X0 : $i]:
% 24.56/24.84         (((sk_A) != (k1_relat_1 @ X0))
% 24.56/24.84          | ~ (v1_relat_1 @ sk_C_2)
% 24.56/24.84          | ~ (v1_funct_1 @ sk_C_2)
% 24.56/24.84          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 24.56/24.84          | ((sk_C_2) = (X0))
% 24.56/24.84          | ~ (v1_funct_1 @ X0)
% 24.56/24.84          | ~ (v1_relat_1 @ X0))),
% 24.56/24.84      inference('sup-', [status(thm)], ['72', '73'])).
% 24.56/24.84  thf('75', plain,
% 24.56/24.84      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.84  thf(cc1_relset_1, axiom,
% 24.56/24.84    (![A:$i,B:$i,C:$i]:
% 24.56/24.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.56/24.84       ( v1_relat_1 @ C ) ))).
% 24.56/24.84  thf('76', plain,
% 24.56/24.84      (![X30 : $i, X31 : $i, X32 : $i]:
% 24.56/24.84         ((v1_relat_1 @ X30)
% 24.56/24.84          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 24.56/24.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 24.56/24.84  thf('77', plain, ((v1_relat_1 @ sk_C_2)),
% 24.56/24.84      inference('sup-', [status(thm)], ['75', '76'])).
% 24.56/24.84  thf('78', plain, ((v1_funct_1 @ sk_C_2)),
% 24.56/24.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.84  thf('79', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 24.56/24.84      inference('demod', [status(thm)], ['66', '71'])).
% 24.56/24.84  thf('80', plain,
% 24.56/24.84      (![X0 : $i]:
% 24.56/24.84         (((sk_A) != (k1_relat_1 @ X0))
% 24.56/24.84          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 24.56/24.84          | ((sk_C_2) = (X0))
% 24.56/24.84          | ~ (v1_funct_1 @ X0)
% 24.56/24.84          | ~ (v1_relat_1 @ X0))),
% 24.56/24.84      inference('demod', [status(thm)], ['74', '77', '78', '79'])).
% 24.56/24.84  thf('81', plain,
% 24.56/24.84      ((((sk_A) != (sk_A))
% 24.56/24.84        | ~ (v1_relat_1 @ sk_D)
% 24.56/24.84        | ~ (v1_funct_1 @ sk_D)
% 24.56/24.84        | ((sk_C_2) = (sk_D))
% 24.56/24.84        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 24.56/24.84      inference('sup-', [status(thm)], ['59', '80'])).
% 24.56/24.84  thf('82', plain,
% 24.56/24.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.84  thf('83', plain,
% 24.56/24.84      (![X30 : $i, X31 : $i, X32 : $i]:
% 24.56/24.84         ((v1_relat_1 @ X30)
% 24.56/24.84          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 24.56/24.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 24.56/24.84  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 24.56/24.84      inference('sup-', [status(thm)], ['82', '83'])).
% 24.56/24.84  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 24.56/24.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.84  thf('86', plain,
% 24.56/24.84      ((((sk_A) != (sk_A))
% 24.56/24.84        | ((sk_C_2) = (sk_D))
% 24.56/24.84        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 24.56/24.84      inference('demod', [status(thm)], ['81', '84', '85'])).
% 24.56/24.84  thf('87', plain,
% 24.56/24.84      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 24.56/24.84      inference('simplify', [status(thm)], ['86'])).
% 24.56/24.84  thf(t1_subset, axiom,
% 24.56/24.84    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 24.56/24.84  thf('88', plain,
% 24.56/24.84      (![X15 : $i, X16 : $i]:
% 24.56/24.84         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 24.56/24.84      inference('cnf', [status(esa)], [t1_subset])).
% 24.56/24.84  thf('89', plain,
% 24.56/24.84      ((((sk_C_2) = (sk_D)) | (m1_subset_1 @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 24.56/24.84      inference('sup-', [status(thm)], ['87', '88'])).
% 24.56/24.84  thf('90', plain,
% 24.56/24.84      (![X54 : $i]:
% 24.56/24.84         (((k1_funct_1 @ sk_C_2 @ X54) = (k1_funct_1 @ sk_D @ X54))
% 24.56/24.84          | ~ (m1_subset_1 @ X54 @ sk_A))),
% 24.56/24.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.84  thf('91', plain,
% 24.56/24.84      ((((sk_C_2) = (sk_D))
% 24.56/24.84        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 24.56/24.84            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 24.56/24.84      inference('sup-', [status(thm)], ['89', '90'])).
% 24.56/24.84  thf('92', plain,
% 24.56/24.84      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 24.56/24.84         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 24.56/24.84      inference('condensation', [status(thm)], ['91'])).
% 24.56/24.84  thf('93', plain,
% 24.56/24.84      (![X26 : $i, X27 : $i]:
% 24.56/24.84         (~ (v1_relat_1 @ X26)
% 24.56/24.84          | ~ (v1_funct_1 @ X26)
% 24.56/24.84          | ((X27) = (X26))
% 24.56/24.84          | ((k1_funct_1 @ X27 @ (sk_C_1 @ X26 @ X27))
% 24.56/24.84              != (k1_funct_1 @ X26 @ (sk_C_1 @ X26 @ X27)))
% 24.56/24.84          | ((k1_relat_1 @ X27) != (k1_relat_1 @ X26))
% 24.56/24.84          | ~ (v1_funct_1 @ X27)
% 24.56/24.84          | ~ (v1_relat_1 @ X27))),
% 24.56/24.84      inference('cnf', [status(esa)], [t9_funct_1])).
% 24.56/24.84  thf('94', plain,
% 24.56/24.84      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 24.56/24.84          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 24.56/24.84        | ~ (v1_relat_1 @ sk_C_2)
% 24.56/24.84        | ~ (v1_funct_1 @ sk_C_2)
% 24.56/24.84        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 24.56/24.84        | ((sk_C_2) = (sk_D))
% 24.56/24.84        | ~ (v1_funct_1 @ sk_D)
% 24.56/24.84        | ~ (v1_relat_1 @ sk_D))),
% 24.56/24.84      inference('sup-', [status(thm)], ['92', '93'])).
% 24.56/24.84  thf('95', plain, ((v1_relat_1 @ sk_C_2)),
% 24.56/24.84      inference('sup-', [status(thm)], ['75', '76'])).
% 24.56/24.84  thf('96', plain, ((v1_funct_1 @ sk_C_2)),
% 24.56/24.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.84  thf('97', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 24.56/24.84      inference('demod', [status(thm)], ['66', '71'])).
% 24.56/24.84  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 24.56/24.84      inference('demod', [status(thm)], ['7', '58'])).
% 24.56/24.84  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 24.56/24.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.84  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 24.56/24.84      inference('sup-', [status(thm)], ['82', '83'])).
% 24.56/24.84  thf('101', plain,
% 24.56/24.84      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 24.56/24.84          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 24.56/24.84        | ((sk_A) != (sk_A))
% 24.56/24.84        | ((sk_C_2) = (sk_D)))),
% 24.56/24.84      inference('demod', [status(thm)],
% 24.56/24.84                ['94', '95', '96', '97', '98', '99', '100'])).
% 24.56/24.84  thf('102', plain, (((sk_C_2) = (sk_D))),
% 24.56/24.84      inference('simplify', [status(thm)], ['101'])).
% 24.56/24.84  thf('103', plain,
% 24.56/24.84      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 24.56/24.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.56/24.84  thf('104', plain,
% 24.56/24.84      (![X43 : $i, X44 : $i, X45 : $i]:
% 24.56/24.84         ((r2_relset_1 @ X43 @ X44 @ X45 @ X45)
% 24.56/24.84          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 24.56/24.84      inference('simplify', [status(thm)], ['34'])).
% 24.56/24.84  thf('105', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 24.56/24.84      inference('sup-', [status(thm)], ['103', '104'])).
% 24.56/24.84  thf('106', plain, ($false),
% 24.56/24.84      inference('demod', [status(thm)], ['0', '102', '105'])).
% 24.56/24.84  
% 24.56/24.84  % SZS output end Refutation
% 24.56/24.84  
% 24.56/24.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
