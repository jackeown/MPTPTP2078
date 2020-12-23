%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EVE17qAFq3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:16 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 388 expanded)
%              Number of leaves         :   51 ( 138 expanded)
%              Depth                    :   20
%              Number of atoms          : 1248 (3508 expanded)
%              Number of equality atoms :  111 ( 290 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_6_type,type,(
    zip_tseitin_6: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t11_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C_3 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X40 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k2_relset_1 @ X47 @ X48 @ X46 )
        = ( k2_relat_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['5','8'])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_6 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf('10',plain,(
    ! [X57: $i,X58: $i,X59: $i,X61: $i] :
      ( ( zip_tseitin_6 @ X57 @ X59 @ X58 @ X61 )
      | ~ ( v1_relat_1 @ X57 )
      | ~ ( v1_funct_1 @ X57 )
      | ( X59 != X57 )
      | ( ( k1_relat_1 @ X57 )
       != X61 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X57 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X57 ) @ X58 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 )
      | ( zip_tseitin_6 @ X57 @ X57 @ X58 @ ( k1_relat_1 @ X57 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( zip_tseitin_6 @ sk_C_3 @ sk_C_3 @ sk_B_1 @ ( k1_relat_1 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    zip_tseitin_6 @ sk_C_3 @ sk_C_3 @ sk_B_1 @ ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['12','15','16'])).

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
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf('18',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_4 @ X49 @ X50 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(rc1_relset_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( v1_xboole_0 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X70: $i,X71: $i] :
      ( v1_xboole_0 @ ( sk_C_2 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_4 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
      = sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ sk_B_1 @ X0 )
      | ( ( k2_relat_1 @ sk_C_3 )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_4 @ B @ A )
         => ( zip_tseitin_5 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_4 @ X54 @ X55 )
      | ( zip_tseitin_5 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('41',plain,
    ( ( zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_4 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = sk_B_1 )
    | ( zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ( X51
        = ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ~ ( zip_tseitin_5 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('45',plain,
    ( ~ ( zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relset_1 @ X44 @ X45 @ X43 )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_4 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('52',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('54',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ sk_B_1 @ X0 )
      | ( ( k2_relat_1 @ sk_C_3 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,
    ( ( zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_4 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('65',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = k1_xboole_0 )
    | ( zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( v5_relat_1 @ sk_C_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( v5_relat_1 @ sk_C_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup+',[status(thm)],['50','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('80',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('84',plain,(
    ~ ( r2_hidden @ sk_C_3 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( r2_hidden @ sk_C_3 @ ( k1_funct_2 @ k1_xboole_0 @ sk_B_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('87',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('89',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,
    ( ( r1_tarski @ sk_C_3 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_3 )
      | ( k1_xboole_0 = sk_C_3 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('97',plain,
    ( ( k1_xboole_0 = sk_C_3 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ sk_B_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','97'])).

thf('99',plain,
    ( ( k1_xboole_0 = sk_C_3 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('100',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X70: $i,X71: $i] :
      ( v5_relat_1 @ ( sk_C_2 @ X70 @ X71 ) @ X70 ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('103',plain,(
    ! [X70: $i,X71: $i] :
      ( v1_xboole_0 @ ( sk_C_2 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X70: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X70 ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('110',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('111',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('114',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X57 ) @ X58 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 )
      | ( zip_tseitin_6 @ X57 @ X57 @ X58 @ ( k1_relat_1 @ X57 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_6 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('118',plain,(
    ! [X70: $i,X71: $i] :
      ( v4_relat_1 @ ( sk_C_2 @ X70 @ X71 ) @ X71 ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_2 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('120',plain,(
    ! [X71: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X71 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('121',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['109','110'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('126',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['109','110'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_6 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['116','117','126','127'])).

thf('129',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_6 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','128'])).

thf(zf_stmt_7,type,(
    zip_tseitin_6: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_6 @ E @ D @ B @ A ) ) ) )).

thf('130',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( zip_tseitin_6 @ X62 @ X63 @ X64 @ X65 )
      | ( r2_hidden @ X63 @ X66 )
      | ( X66
       != ( k1_funct_2 @ X65 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('131',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( r2_hidden @ X63 @ ( k1_funct_2 @ X65 @ X64 ) )
      | ~ ( zip_tseitin_6 @ X62 @ X63 @ X64 @ X65 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['98','132'])).

thf('134',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('135',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['133','134'])).

thf('136',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['82','135'])).

thf('137',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['80','136'])).

thf('138',plain,(
    zip_tseitin_6 @ sk_C_3 @ sk_C_3 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['17','137'])).

thf('139',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( r2_hidden @ X63 @ ( k1_funct_2 @ X65 @ X64 ) )
      | ~ ( zip_tseitin_6 @ X62 @ X63 @ X64 @ X65 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('140',plain,(
    r2_hidden @ sk_C_3 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['0','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EVE17qAFq3
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.70/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.91  % Solved by: fo/fo7.sh
% 0.70/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.91  % done 708 iterations in 0.463s
% 0.70/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.91  % SZS output start Refutation
% 0.70/0.91  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.70/0.91  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.70/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.70/0.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.70/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.70/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.70/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.70/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.70/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.91  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.70/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.91  thf(sk_B_type, type, sk_B: $i > $i).
% 0.70/0.91  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.70/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.91  thf(zip_tseitin_6_type, type, zip_tseitin_6: $i > $i > $i > $i > $o).
% 0.70/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.91  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.70/0.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.91  thf(t11_funct_2, conjecture,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.91         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.70/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.91          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.91            ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )),
% 0.70/0.91    inference('cnf.neg', [status(esa)], [t11_funct_2])).
% 0.70/0.91  thf('0', plain, (~ (r2_hidden @ sk_C_3 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('1', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(dt_k2_relset_1, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.91       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.70/0.91  thf('2', plain,
% 0.70/0.91      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.70/0.91         ((m1_subset_1 @ (k2_relset_1 @ X40 @ X41 @ X42) @ (k1_zfmisc_1 @ X41))
% 0.70/0.91          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.70/0.91  thf('3', plain,
% 0.70/0.91      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) @ 
% 0.70/0.91        (k1_zfmisc_1 @ sk_B_1))),
% 0.70/0.91      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.91  thf(t3_subset, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.91  thf('4', plain,
% 0.70/0.91      (![X14 : $i, X15 : $i]:
% 0.70/0.91         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.70/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.91  thf('5', plain,
% 0.70/0.91      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) @ sk_B_1)),
% 0.70/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.91  thf('6', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(redefinition_k2_relset_1, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.70/0.91  thf('7', plain,
% 0.70/0.91      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.70/0.91         (((k2_relset_1 @ X47 @ X48 @ X46) = (k2_relat_1 @ X46))
% 0.70/0.91          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 0.70/0.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.70/0.91  thf('8', plain,
% 0.70/0.91      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.70/0.91      inference('sup-', [status(thm)], ['6', '7'])).
% 0.70/0.91  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B_1)),
% 0.70/0.91      inference('demod', [status(thm)], ['5', '8'])).
% 0.70/0.91  thf(d2_funct_2, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.70/0.91       ( ![D:$i]:
% 0.70/0.91         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.91           ( ?[E:$i]:
% 0.70/0.91             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.70/0.91               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.70/0.91               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.70/0.91  thf(zf_stmt_1, axiom,
% 0.70/0.91    (![E:$i,D:$i,B:$i,A:$i]:
% 0.70/0.91     ( ( zip_tseitin_6 @ E @ D @ B @ A ) <=>
% 0.70/0.91       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.70/0.91         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.70/0.91         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.70/0.91  thf('10', plain,
% 0.70/0.91      (![X57 : $i, X58 : $i, X59 : $i, X61 : $i]:
% 0.70/0.91         ((zip_tseitin_6 @ X57 @ X59 @ X58 @ X61)
% 0.70/0.91          | ~ (v1_relat_1 @ X57)
% 0.70/0.91          | ~ (v1_funct_1 @ X57)
% 0.70/0.91          | ((X59) != (X57))
% 0.70/0.91          | ((k1_relat_1 @ X57) != (X61))
% 0.70/0.91          | ~ (r1_tarski @ (k2_relat_1 @ X57) @ X58))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.70/0.91  thf('11', plain,
% 0.70/0.91      (![X57 : $i, X58 : $i]:
% 0.70/0.91         (~ (r1_tarski @ (k2_relat_1 @ X57) @ X58)
% 0.70/0.91          | ~ (v1_funct_1 @ X57)
% 0.70/0.91          | ~ (v1_relat_1 @ X57)
% 0.70/0.91          | (zip_tseitin_6 @ X57 @ X57 @ X58 @ (k1_relat_1 @ X57)))),
% 0.70/0.91      inference('simplify', [status(thm)], ['10'])).
% 0.70/0.91  thf('12', plain,
% 0.70/0.91      (((zip_tseitin_6 @ sk_C_3 @ sk_C_3 @ sk_B_1 @ (k1_relat_1 @ sk_C_3))
% 0.70/0.91        | ~ (v1_relat_1 @ sk_C_3)
% 0.70/0.91        | ~ (v1_funct_1 @ sk_C_3))),
% 0.70/0.91      inference('sup-', [status(thm)], ['9', '11'])).
% 0.70/0.91  thf('13', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(cc1_relset_1, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.91       ( v1_relat_1 @ C ) ))).
% 0.70/0.91  thf('14', plain,
% 0.70/0.91      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.70/0.91         ((v1_relat_1 @ X34)
% 0.70/0.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.70/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.70/0.91  thf('15', plain, ((v1_relat_1 @ sk_C_3)),
% 0.70/0.91      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.91  thf('16', plain, ((v1_funct_1 @ sk_C_3)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('17', plain,
% 0.70/0.91      ((zip_tseitin_6 @ sk_C_3 @ sk_C_3 @ sk_B_1 @ (k1_relat_1 @ sk_C_3))),
% 0.70/0.91      inference('demod', [status(thm)], ['12', '15', '16'])).
% 0.70/0.91  thf(d1_funct_2, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.70/0.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.70/0.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.70/0.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.70/0.91  thf(zf_stmt_2, axiom,
% 0.70/0.91    (![B:$i,A:$i]:
% 0.70/0.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.91       ( zip_tseitin_4 @ B @ A ) ))).
% 0.70/0.91  thf('18', plain,
% 0.70/0.91      (![X49 : $i, X50 : $i]:
% 0.70/0.91         ((zip_tseitin_4 @ X49 @ X50) | ((X49) = (k1_xboole_0)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.91  thf(rc1_relset_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ?[C:$i]:
% 0.70/0.91       ( ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 0.70/0.91         ( v1_relat_1 @ C ) & ( v1_xboole_0 @ C ) & 
% 0.70/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.70/0.91  thf('19', plain,
% 0.70/0.91      (![X70 : $i, X71 : $i]: (v1_xboole_0 @ (sk_C_2 @ X70 @ X71))),
% 0.70/0.91      inference('cnf', [status(esa)], [rc1_relset_1])).
% 0.70/0.91  thf(d1_xboole_0, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.70/0.91  thf('20', plain,
% 0.70/0.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.70/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.70/0.91  thf('21', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.70/0.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.91  thf(d3_tarski, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.91  thf('22', plain,
% 0.70/0.91      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.70/0.91         (~ (r2_hidden @ X3 @ X4)
% 0.70/0.91          | (r2_hidden @ X3 @ X5)
% 0.70/0.91          | ~ (r1_tarski @ X4 @ X5))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.91  thf('23', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['21', '22'])).
% 0.70/0.91  thf('24', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['20', '23'])).
% 0.70/0.91  thf('25', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.91  thf('26', plain,
% 0.70/0.91      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['24', '25'])).
% 0.70/0.91  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.91      inference('sup-', [status(thm)], ['19', '26'])).
% 0.70/0.91  thf('28', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_4 @ X0 @ X1))),
% 0.70/0.91      inference('sup+', [status(thm)], ['18', '27'])).
% 0.70/0.91  thf('29', plain,
% 0.70/0.91      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) @ sk_B_1)),
% 0.70/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.91  thf('30', plain,
% 0.70/0.91      (![X4 : $i, X6 : $i]:
% 0.70/0.91         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.91  thf('31', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.91  thf('32', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['30', '31'])).
% 0.70/0.91  thf(d10_xboole_0, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.91  thf('33', plain,
% 0.70/0.91      (![X7 : $i, X9 : $i]:
% 0.70/0.91         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('34', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['32', '33'])).
% 0.70/0.91  thf('35', plain,
% 0.70/0.91      ((((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) = (sk_B_1))
% 0.70/0.91        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.70/0.91      inference('sup-', [status(thm)], ['29', '34'])).
% 0.70/0.91  thf('36', plain,
% 0.70/0.91      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.70/0.91      inference('sup-', [status(thm)], ['6', '7'])).
% 0.70/0.91  thf('37', plain,
% 0.70/0.91      ((((k2_relat_1 @ sk_C_3) = (sk_B_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.70/0.91      inference('demod', [status(thm)], ['35', '36'])).
% 0.70/0.91  thf('38', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((zip_tseitin_4 @ sk_B_1 @ X0) | ((k2_relat_1 @ sk_C_3) = (sk_B_1)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['28', '37'])).
% 0.70/0.91  thf('39', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(zf_stmt_3, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.70/0.91  thf(zf_stmt_4, axiom,
% 0.70/0.91    (![C:$i,B:$i,A:$i]:
% 0.70/0.91     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.70/0.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.70/0.91  thf(zf_stmt_5, type, zip_tseitin_4 : $i > $i > $o).
% 0.70/0.91  thf(zf_stmt_6, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.91       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.70/0.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.70/0.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.70/0.91  thf('40', plain,
% 0.70/0.91      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.70/0.91         (~ (zip_tseitin_4 @ X54 @ X55)
% 0.70/0.91          | (zip_tseitin_5 @ X56 @ X54 @ X55)
% 0.70/0.91          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.70/0.91  thf('41', plain,
% 0.70/0.91      (((zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A)
% 0.70/0.91        | ~ (zip_tseitin_4 @ sk_B_1 @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['39', '40'])).
% 0.70/0.91  thf('42', plain,
% 0.70/0.91      ((((k2_relat_1 @ sk_C_3) = (sk_B_1))
% 0.70/0.91        | (zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['38', '41'])).
% 0.70/0.91  thf('43', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_1)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('44', plain,
% 0.70/0.91      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.70/0.91         (~ (v1_funct_2 @ X53 @ X51 @ X52)
% 0.70/0.91          | ((X51) = (k1_relset_1 @ X51 @ X52 @ X53))
% 0.70/0.91          | ~ (zip_tseitin_5 @ X53 @ X52 @ X51))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.70/0.91  thf('45', plain,
% 0.70/0.91      ((~ (zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A)
% 0.70/0.91        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_3)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.70/0.91  thf('46', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(redefinition_k1_relset_1, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.91       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.70/0.91  thf('47', plain,
% 0.70/0.91      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.70/0.91         (((k1_relset_1 @ X44 @ X45 @ X43) = (k1_relat_1 @ X43))
% 0.70/0.91          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.70/0.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.91  thf('48', plain,
% 0.70/0.91      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.70/0.91      inference('sup-', [status(thm)], ['46', '47'])).
% 0.70/0.91  thf('49', plain,
% 0.70/0.91      ((~ (zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A)
% 0.70/0.91        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 0.70/0.91      inference('demod', [status(thm)], ['45', '48'])).
% 0.70/0.91  thf('50', plain,
% 0.70/0.91      ((((k2_relat_1 @ sk_C_3) = (sk_B_1)) | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['42', '49'])).
% 0.70/0.91  thf('51', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_4 @ X0 @ X1))),
% 0.70/0.91      inference('sup+', [status(thm)], ['18', '27'])).
% 0.70/0.91  thf('52', plain,
% 0.70/0.91      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) @ sk_B_1)),
% 0.70/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.91  thf('53', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['30', '31'])).
% 0.70/0.91  thf('54', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.70/0.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.91  thf('55', plain,
% 0.70/0.91      (![X7 : $i, X9 : $i]:
% 0.70/0.91         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('56', plain,
% 0.70/0.91      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['54', '55'])).
% 0.70/0.91  thf('57', plain,
% 0.70/0.91      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['53', '56'])).
% 0.70/0.91  thf('58', plain,
% 0.70/0.91      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['54', '55'])).
% 0.70/0.91  thf('59', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X1 @ X0)
% 0.70/0.91          | ~ (v1_xboole_0 @ X0)
% 0.70/0.91          | ((X1) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['57', '58'])).
% 0.70/0.91  thf('60', plain,
% 0.70/0.91      ((((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) = (k1_xboole_0))
% 0.70/0.91        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.70/0.91      inference('sup-', [status(thm)], ['52', '59'])).
% 0.70/0.91  thf('61', plain,
% 0.70/0.91      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.70/0.91      inference('sup-', [status(thm)], ['6', '7'])).
% 0.70/0.91  thf('62', plain,
% 0.70/0.91      ((((k2_relat_1 @ sk_C_3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.70/0.91      inference('demod', [status(thm)], ['60', '61'])).
% 0.70/0.91  thf('63', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((zip_tseitin_4 @ sk_B_1 @ X0)
% 0.70/0.91          | ((k2_relat_1 @ sk_C_3) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['51', '62'])).
% 0.70/0.91  thf('64', plain,
% 0.70/0.91      (((zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A)
% 0.70/0.91        | ~ (zip_tseitin_4 @ sk_B_1 @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['39', '40'])).
% 0.70/0.92  thf('65', plain,
% 0.70/0.92      ((((k2_relat_1 @ sk_C_3) = (k1_xboole_0))
% 0.70/0.92        | (zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['63', '64'])).
% 0.70/0.92  thf('66', plain,
% 0.70/0.92      ((~ (zip_tseitin_5 @ sk_C_3 @ sk_B_1 @ sk_A)
% 0.70/0.92        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 0.70/0.92      inference('demod', [status(thm)], ['45', '48'])).
% 0.70/0.92  thf('67', plain,
% 0.70/0.92      ((((k2_relat_1 @ sk_C_3) = (k1_xboole_0))
% 0.70/0.92        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['65', '66'])).
% 0.70/0.92  thf(d19_relat_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( v1_relat_1 @ B ) =>
% 0.70/0.92       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.70/0.92  thf('68', plain,
% 0.70/0.92      (![X19 : $i, X20 : $i]:
% 0.70/0.92         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.70/0.92          | (v5_relat_1 @ X19 @ X20)
% 0.70/0.92          | ~ (v1_relat_1 @ X19))),
% 0.70/0.92      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.70/0.92  thf('69', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.70/0.92          | ((sk_A) = (k1_relat_1 @ sk_C_3))
% 0.70/0.92          | ~ (v1_relat_1 @ sk_C_3)
% 0.70/0.92          | (v5_relat_1 @ sk_C_3 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['67', '68'])).
% 0.70/0.92  thf('70', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.70/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.92  thf('71', plain, ((v1_relat_1 @ sk_C_3)),
% 0.70/0.92      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.92  thf('72', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((sk_A) = (k1_relat_1 @ sk_C_3)) | (v5_relat_1 @ sk_C_3 @ X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.70/0.92  thf('73', plain,
% 0.70/0.92      (![X19 : $i, X20 : $i]:
% 0.70/0.92         (~ (v5_relat_1 @ X19 @ X20)
% 0.70/0.92          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.70/0.92          | ~ (v1_relat_1 @ X19))),
% 0.70/0.92      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.70/0.92  thf('74', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((sk_A) = (k1_relat_1 @ sk_C_3))
% 0.70/0.92          | ~ (v1_relat_1 @ sk_C_3)
% 0.70/0.92          | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['72', '73'])).
% 0.70/0.92  thf('75', plain, ((v1_relat_1 @ sk_C_3)),
% 0.70/0.92      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.92  thf('76', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((sk_A) = (k1_relat_1 @ sk_C_3))
% 0.70/0.92          | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['74', '75'])).
% 0.70/0.92  thf('77', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((r1_tarski @ sk_B_1 @ X0)
% 0.70/0.92          | ((sk_A) = (k1_relat_1 @ sk_C_3))
% 0.70/0.92          | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['50', '76'])).
% 0.70/0.92  thf('78', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((sk_A) = (k1_relat_1 @ sk_C_3)) | (r1_tarski @ sk_B_1 @ X0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['77'])).
% 0.70/0.92  thf('79', plain,
% 0.70/0.92      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['54', '55'])).
% 0.70/0.92  thf('80', plain,
% 0.70/0.92      ((((sk_A) = (k1_relat_1 @ sk_C_3)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['78', '79'])).
% 0.70/0.92  thf('81', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('82', plain,
% 0.70/0.92      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.70/0.92      inference('split', [status(esa)], ['81'])).
% 0.70/0.92  thf('83', plain,
% 0.70/0.92      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('split', [status(esa)], ['81'])).
% 0.70/0.92  thf('84', plain, (~ (r2_hidden @ sk_C_3 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('85', plain,
% 0.70/0.92      ((~ (r2_hidden @ sk_C_3 @ (k1_funct_2 @ k1_xboole_0 @ sk_B_1)))
% 0.70/0.92         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['83', '84'])).
% 0.70/0.92  thf(t113_zfmisc_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.70/0.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.70/0.92  thf('86', plain,
% 0.70/0.92      (![X12 : $i, X13 : $i]:
% 0.70/0.92         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.70/0.92          | ((X12) != (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.70/0.92  thf('87', plain,
% 0.70/0.92      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['86'])).
% 0.70/0.92  thf('88', plain,
% 0.70/0.92      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('split', [status(esa)], ['81'])).
% 0.70/0.92  thf('89', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('90', plain,
% 0.70/0.92      (((m1_subset_1 @ sk_C_3 @ 
% 0.70/0.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.70/0.92         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['88', '89'])).
% 0.70/0.92  thf('91', plain,
% 0.70/0.92      (((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.70/0.92         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['87', '90'])).
% 0.70/0.92  thf('92', plain,
% 0.70/0.92      (![X14 : $i, X15 : $i]:
% 0.70/0.92         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.92  thf('93', plain,
% 0.70/0.92      (((r1_tarski @ sk_C_3 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['91', '92'])).
% 0.70/0.92  thf('94', plain,
% 0.70/0.92      (![X7 : $i, X9 : $i]:
% 0.70/0.92         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.70/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.92  thf('95', plain,
% 0.70/0.92      (((~ (r1_tarski @ k1_xboole_0 @ sk_C_3) | ((k1_xboole_0) = (sk_C_3))))
% 0.70/0.92         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['93', '94'])).
% 0.70/0.92  thf('96', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.70/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.92  thf('97', plain,
% 0.70/0.92      ((((k1_xboole_0) = (sk_C_3))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('demod', [status(thm)], ['95', '96'])).
% 0.70/0.92  thf('98', plain,
% 0.70/0.92      ((~ (r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ sk_B_1)))
% 0.70/0.92         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('demod', [status(thm)], ['85', '97'])).
% 0.70/0.92  thf('99', plain,
% 0.70/0.92      ((((k1_xboole_0) = (sk_C_3))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('demod', [status(thm)], ['95', '96'])).
% 0.70/0.92  thf('100', plain, ((v1_funct_1 @ sk_C_3)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('101', plain,
% 0.70/0.92      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['99', '100'])).
% 0.70/0.92  thf('102', plain,
% 0.70/0.92      (![X70 : $i, X71 : $i]: (v5_relat_1 @ (sk_C_2 @ X70 @ X71) @ X70)),
% 0.70/0.92      inference('cnf', [status(esa)], [rc1_relset_1])).
% 0.70/0.92  thf('103', plain,
% 0.70/0.92      (![X70 : $i, X71 : $i]: (v1_xboole_0 @ (sk_C_2 @ X70 @ X71))),
% 0.70/0.92      inference('cnf', [status(esa)], [rc1_relset_1])).
% 0.70/0.92  thf('104', plain,
% 0.70/0.92      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['53', '56'])).
% 0.70/0.92  thf('105', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((sk_C_2 @ X1 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['103', '104'])).
% 0.70/0.92  thf('106', plain, (![X70 : $i]: (v5_relat_1 @ k1_xboole_0 @ X70)),
% 0.70/0.92      inference('demod', [status(thm)], ['102', '105'])).
% 0.70/0.92  thf('107', plain,
% 0.70/0.92      (![X19 : $i, X20 : $i]:
% 0.70/0.92         (~ (v5_relat_1 @ X19 @ X20)
% 0.70/0.92          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.70/0.92          | ~ (v1_relat_1 @ X19))),
% 0.70/0.92      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.70/0.92  thf('108', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['106', '107'])).
% 0.70/0.92  thf('109', plain,
% 0.70/0.92      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['86'])).
% 0.70/0.92  thf(fc6_relat_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.70/0.92  thf('110', plain,
% 0.70/0.92      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.70/0.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.70/0.92  thf('111', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.70/0.92      inference('sup+', [status(thm)], ['109', '110'])).
% 0.70/0.92  thf('112', plain,
% 0.70/0.92      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.70/0.92      inference('demod', [status(thm)], ['108', '111'])).
% 0.70/0.92  thf('113', plain,
% 0.70/0.92      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['54', '55'])).
% 0.70/0.92  thf('114', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['112', '113'])).
% 0.70/0.92  thf('115', plain,
% 0.70/0.92      (![X57 : $i, X58 : $i]:
% 0.70/0.92         (~ (r1_tarski @ (k2_relat_1 @ X57) @ X58)
% 0.70/0.92          | ~ (v1_funct_1 @ X57)
% 0.70/0.92          | ~ (v1_relat_1 @ X57)
% 0.70/0.92          | (zip_tseitin_6 @ X57 @ X57 @ X58 @ (k1_relat_1 @ X57)))),
% 0.70/0.92      inference('simplify', [status(thm)], ['10'])).
% 0.70/0.92  thf('116', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.70/0.92          | (zip_tseitin_6 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ 
% 0.70/0.92             (k1_relat_1 @ k1_xboole_0))
% 0.70/0.92          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['114', '115'])).
% 0.70/0.92  thf('117', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.70/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.92  thf('118', plain,
% 0.70/0.92      (![X70 : $i, X71 : $i]: (v4_relat_1 @ (sk_C_2 @ X70 @ X71) @ X71)),
% 0.70/0.92      inference('cnf', [status(esa)], [rc1_relset_1])).
% 0.70/0.92  thf('119', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((sk_C_2 @ X1 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['103', '104'])).
% 0.70/0.92  thf('120', plain, (![X71 : $i]: (v4_relat_1 @ k1_xboole_0 @ X71)),
% 0.70/0.92      inference('demod', [status(thm)], ['118', '119'])).
% 0.70/0.92  thf(d18_relat_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( v1_relat_1 @ B ) =>
% 0.70/0.92       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.70/0.92  thf('121', plain,
% 0.70/0.92      (![X17 : $i, X18 : $i]:
% 0.70/0.92         (~ (v4_relat_1 @ X17 @ X18)
% 0.70/0.92          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.70/0.92          | ~ (v1_relat_1 @ X17))),
% 0.70/0.92      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.70/0.92  thf('122', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['120', '121'])).
% 0.70/0.92  thf('123', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.70/0.92      inference('sup+', [status(thm)], ['109', '110'])).
% 0.70/0.92  thf('124', plain,
% 0.70/0.92      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.70/0.92      inference('demod', [status(thm)], ['122', '123'])).
% 0.70/0.92  thf('125', plain,
% 0.70/0.92      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['54', '55'])).
% 0.70/0.92  thf('126', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['124', '125'])).
% 0.70/0.92  thf('127', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.70/0.92      inference('sup+', [status(thm)], ['109', '110'])).
% 0.70/0.92  thf('128', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((zip_tseitin_6 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['116', '117', '126', '127'])).
% 0.70/0.92  thf('129', plain,
% 0.70/0.92      ((![X0 : $i]:
% 0.70/0.92          (zip_tseitin_6 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0))
% 0.70/0.92         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['101', '128'])).
% 0.70/0.92  thf(zf_stmt_7, type, zip_tseitin_6 : $i > $i > $i > $i > $o).
% 0.70/0.92  thf(zf_stmt_8, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.70/0.92       ( ![D:$i]:
% 0.70/0.92         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.92           ( ?[E:$i]: ( zip_tseitin_6 @ E @ D @ B @ A ) ) ) ) ))).
% 0.70/0.92  thf('130', plain,
% 0.70/0.92      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 0.70/0.92         (~ (zip_tseitin_6 @ X62 @ X63 @ X64 @ X65)
% 0.70/0.92          | (r2_hidden @ X63 @ X66)
% 0.70/0.92          | ((X66) != (k1_funct_2 @ X65 @ X64)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.70/0.92  thf('131', plain,
% 0.70/0.92      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.70/0.92         ((r2_hidden @ X63 @ (k1_funct_2 @ X65 @ X64))
% 0.70/0.92          | ~ (zip_tseitin_6 @ X62 @ X63 @ X64 @ X65))),
% 0.70/0.92      inference('simplify', [status(thm)], ['130'])).
% 0.70/0.92  thf('132', plain,
% 0.70/0.92      ((![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ X0)))
% 0.70/0.92         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['129', '131'])).
% 0.70/0.92  thf('133', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['98', '132'])).
% 0.70/0.92  thf('134', plain,
% 0.70/0.92      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.70/0.92      inference('split', [status(esa)], ['81'])).
% 0.70/0.92  thf('135', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.70/0.92      inference('sat_resolution*', [status(thm)], ['133', '134'])).
% 0.70/0.92  thf('136', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.70/0.92      inference('simpl_trail', [status(thm)], ['82', '135'])).
% 0.70/0.92  thf('137', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 0.70/0.92      inference('simplify_reflect-', [status(thm)], ['80', '136'])).
% 0.70/0.92  thf('138', plain, ((zip_tseitin_6 @ sk_C_3 @ sk_C_3 @ sk_B_1 @ sk_A)),
% 0.70/0.92      inference('demod', [status(thm)], ['17', '137'])).
% 0.70/0.92  thf('139', plain,
% 0.70/0.92      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.70/0.92         ((r2_hidden @ X63 @ (k1_funct_2 @ X65 @ X64))
% 0.70/0.92          | ~ (zip_tseitin_6 @ X62 @ X63 @ X64 @ X65))),
% 0.70/0.92      inference('simplify', [status(thm)], ['130'])).
% 0.70/0.92  thf('140', plain, ((r2_hidden @ sk_C_3 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.70/0.92      inference('sup-', [status(thm)], ['138', '139'])).
% 0.70/0.92  thf('141', plain, ($false), inference('demod', [status(thm)], ['0', '140'])).
% 0.70/0.92  
% 0.70/0.92  % SZS output end Refutation
% 0.70/0.92  
% 0.70/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
