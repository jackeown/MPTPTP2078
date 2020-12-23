%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bJ1hRVuYaz

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:34 EST 2020

% Result     : Theorem 10.81s
% Output     : Refutation 10.81s
% Verified   : 
% Statistics : Number of formulae       :  368 (7369 expanded)
%              Number of leaves         :   49 (2273 expanded)
%              Depth                    :   43
%              Number of atoms          : 2672 (81189 expanded)
%              Number of equality atoms :  232 (4354 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 )
      | ( X33 != X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
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
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('14',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( sk_F @ X37 @ X38 @ X39 ) @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ ( sk_F @ sk_B_1 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_F @ sk_B_1 @ sk_A @ ( sk_B @ sk_C_2 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('34',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( v4_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( X0
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','67'])).

thf('69',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( sk_E @ X37 @ X38 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ X2 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('83',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('88',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('89',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('92',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('94',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('98',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( sk_E @ X37 @ X38 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( sk_E @ X0 @ X1 @ X3 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['95','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','106'])).

thf('108',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('109',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('110',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['81','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['77','114'])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','115'])).

thf('117',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('118',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('122',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('126',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('129',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['123','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('133',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_B_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('137',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','111'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('144',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('147',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('148',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('149',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v4_relat_1 @ sk_D @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','111'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v4_relat_1 @ sk_D @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('155',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('157',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('159',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('161',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('163',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('167',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( ( k1_relat_1 @ sk_D )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['144','174'])).

thf('176',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( v4_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('178',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('187',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( ( k1_relat_1 @ sk_D )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('189',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['176','190'])).

thf('192',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( ( k1_relat_1 @ sk_B_1 )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('195',plain,(
    v4_relat_1 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('199',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('201',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['192','201'])).

thf('203',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['135','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['116','205'])).

thf('207',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('208',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['206','208'])).

thf('210',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('211',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('213',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('214',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['81','113'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['212','221'])).

thf('223',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['211','222'])).

thf('224',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','223'])).

thf('225',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_A ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('227',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('228',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('230',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

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

thf('231',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X21 = X20 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ X21 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('234',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['211','222'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['225','237'])).

thf('239',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('240',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X49: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X49 )
        = ( k1_funct_1 @ sk_D @ X49 ) )
      | ~ ( r2_hidden @ X49 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['244'])).

thf('246',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X21 = X20 )
      | ( ( k1_funct_1 @ X21 @ ( sk_C_1 @ X20 @ X21 ) )
       != ( k1_funct_1 @ X20 @ ( sk_C_1 @ X20 @ X21 ) ) )
      | ( ( k1_relat_1 @ X21 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('247',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('249',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['211','222'])).

thf('251',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_A ),
    inference(simplify,[status(thm)],['224'])).

thf('252',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('254',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['247','248','249','250','251','252','253'])).

thf('255',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('260',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['257','260'])).

thf('262',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','111'])).

thf('263',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['22','261','262'])).

thf('264',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['15','263'])).

thf('265',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('267',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['81','113'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['265','268'])).

thf('270',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('271',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['269','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('275',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 != k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ( X48 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('276',plain,(
    ! [X47: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X47 @ k1_xboole_0 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('278',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('279',plain,(
    ! [X47: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X47 @ k1_xboole_0 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['279','280'])).

thf('282',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('283',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('284',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('286',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['284','285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['281','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['274','288'])).

thf('290',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['273','289'])).

thf('291',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('292',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_A ),
    inference(simplify,[status(thm)],['224'])).

thf('293',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('294',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('295',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_D @ X1 ) ) ),
    inference('sup+',[status(thm)],['292','295'])).

thf('297',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('299',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['81','113'])).

thf('300',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['297','300'])).

thf('302',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_D @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['296','301'])).

thf('303',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','111'])).

thf('304',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_D @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['302','303'])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['291','304'])).

thf('306',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['274','288'])).

thf('309',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('311',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['290','311'])).

thf('313',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['257','260'])).

thf('314',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','111'])).

thf('315',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('316',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','111'])).

thf('317',plain,(
    $false ),
    inference(demod,[status(thm)],['264','315','316'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bJ1hRVuYaz
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:03:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 10.81/11.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.81/11.00  % Solved by: fo/fo7.sh
% 10.81/11.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.81/11.00  % done 10726 iterations in 10.545s
% 10.81/11.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.81/11.00  % SZS output start Refutation
% 10.81/11.00  thf(sk_D_type, type, sk_D: $i).
% 10.81/11.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.81/11.00  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 10.81/11.00  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 10.81/11.00  thf(sk_B_1_type, type, sk_B_1: $i).
% 10.81/11.00  thf(sk_B_type, type, sk_B: $i > $i).
% 10.81/11.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.81/11.00  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 10.81/11.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.81/11.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.81/11.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.81/11.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.81/11.00  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 10.81/11.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.81/11.00  thf(sk_A_type, type, sk_A: $i).
% 10.81/11.00  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.81/11.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.81/11.00  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 10.81/11.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.81/11.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.81/11.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.81/11.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.81/11.00  thf(sk_C_2_type, type, sk_C_2: $i).
% 10.81/11.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.81/11.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 10.81/11.00  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 10.81/11.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.81/11.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.81/11.00  thf(d3_tarski, axiom,
% 10.81/11.00    (![A:$i,B:$i]:
% 10.81/11.00     ( ( r1_tarski @ A @ B ) <=>
% 10.81/11.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 10.81/11.00  thf('0', plain,
% 10.81/11.00      (![X4 : $i, X6 : $i]:
% 10.81/11.00         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 10.81/11.00      inference('cnf', [status(esa)], [d3_tarski])).
% 10.81/11.00  thf(d1_xboole_0, axiom,
% 10.81/11.00    (![A:$i]:
% 10.81/11.00     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 10.81/11.00  thf('1', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf('2', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['0', '1'])).
% 10.81/11.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.81/11.00  thf('3', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 10.81/11.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.81/11.00  thf(d10_xboole_0, axiom,
% 10.81/11.00    (![A:$i,B:$i]:
% 10.81/11.00     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.81/11.00  thf('4', plain,
% 10.81/11.00      (![X7 : $i, X9 : $i]:
% 10.81/11.00         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 10.81/11.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.81/11.00  thf('5', plain,
% 10.81/11.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['3', '4'])).
% 10.81/11.00  thf('6', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['2', '5'])).
% 10.81/11.00  thf('7', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['2', '5'])).
% 10.81/11.00  thf(t4_subset_1, axiom,
% 10.81/11.00    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 10.81/11.00  thf('8', plain,
% 10.81/11.00      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.81/11.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.81/11.00  thf(redefinition_r2_relset_1, axiom,
% 10.81/11.00    (![A:$i,B:$i,C:$i,D:$i]:
% 10.81/11.00     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.81/11.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.81/11.00       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.81/11.00  thf('9', plain,
% 10.81/11.00      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 10.81/11.00          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 10.81/11.00          | (r2_relset_1 @ X34 @ X35 @ X33 @ X36)
% 10.81/11.00          | ((X33) != (X36)))),
% 10.81/11.00      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.81/11.00  thf('10', plain,
% 10.81/11.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 10.81/11.00         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 10.81/11.00          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 10.81/11.00      inference('simplify', [status(thm)], ['9'])).
% 10.81/11.00  thf('11', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['8', '10'])).
% 10.81/11.00  thf('12', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup+', [status(thm)], ['7', '11'])).
% 10.81/11.00  thf('13', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.81/11.00         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 10.81/11.00          | ~ (v1_xboole_0 @ X0)
% 10.81/11.00          | ~ (v1_xboole_0 @ X1))),
% 10.81/11.00      inference('sup+', [status(thm)], ['6', '12'])).
% 10.81/11.00  thf(t18_funct_2, conjecture,
% 10.81/11.00    (![A:$i,B:$i,C:$i]:
% 10.81/11.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.81/11.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.81/11.00       ( ![D:$i]:
% 10.81/11.00         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.81/11.00             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.81/11.00           ( ( ![E:$i]:
% 10.81/11.00               ( ( r2_hidden @ E @ A ) =>
% 10.81/11.00                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 10.81/11.00             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 10.81/11.00  thf(zf_stmt_0, negated_conjecture,
% 10.81/11.00    (~( ![A:$i,B:$i,C:$i]:
% 10.81/11.00        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.81/11.00            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.81/11.00          ( ![D:$i]:
% 10.81/11.00            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.81/11.00                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.81/11.00              ( ( ![E:$i]:
% 10.81/11.00                  ( ( r2_hidden @ E @ A ) =>
% 10.81/11.00                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 10.81/11.00                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 10.81/11.00    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 10.81/11.00  thf('14', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('15', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 10.81/11.00      inference('sup-', [status(thm)], ['13', '14'])).
% 10.81/11.00  thf('16', plain,
% 10.81/11.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf('17', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf(t6_relset_1, axiom,
% 10.81/11.00    (![A:$i,B:$i,C:$i,D:$i]:
% 10.81/11.00     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 10.81/11.00       ( ~( ( r2_hidden @ A @ D ) & 
% 10.81/11.00            ( ![E:$i,F:$i]:
% 10.81/11.00              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 10.81/11.00                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 10.81/11.00  thf('18', plain,
% 10.81/11.00      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 10.81/11.00         ((r2_hidden @ (sk_F @ X37 @ X38 @ X39) @ X37)
% 10.81/11.00          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 10.81/11.00          | ~ (r2_hidden @ X39 @ X40))),
% 10.81/11.00      inference('cnf', [status(esa)], [t6_relset_1])).
% 10.81/11.00  thf('19', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X0 @ sk_C_2)
% 10.81/11.00          | (r2_hidden @ (sk_F @ sk_B_1 @ sk_A @ X0) @ sk_B_1))),
% 10.81/11.00      inference('sup-', [status(thm)], ['17', '18'])).
% 10.81/11.00  thf('20', plain,
% 10.81/11.00      (((v1_xboole_0 @ sk_C_2)
% 10.81/11.00        | (r2_hidden @ (sk_F @ sk_B_1 @ sk_A @ (sk_B @ sk_C_2)) @ sk_B_1))),
% 10.81/11.00      inference('sup-', [status(thm)], ['16', '19'])).
% 10.81/11.00  thf('21', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf('22', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 10.81/11.00      inference('sup-', [status(thm)], ['20', '21'])).
% 10.81/11.00  thf(d1_funct_2, axiom,
% 10.81/11.00    (![A:$i,B:$i,C:$i]:
% 10.81/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.81/11.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.81/11.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.81/11.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.81/11.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.81/11.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.81/11.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.81/11.00  thf(zf_stmt_1, axiom,
% 10.81/11.00    (![B:$i,A:$i]:
% 10.81/11.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.81/11.00       ( zip_tseitin_0 @ B @ A ) ))).
% 10.81/11.00  thf('23', plain,
% 10.81/11.00      (![X41 : $i, X42 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.81/11.00  thf(t113_zfmisc_1, axiom,
% 10.81/11.00    (![A:$i,B:$i]:
% 10.81/11.00     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 10.81/11.00       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 10.81/11.00  thf('24', plain,
% 10.81/11.00      (![X12 : $i, X13 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 10.81/11.00          | ((X13) != (k1_xboole_0)))),
% 10.81/11.00      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.81/11.00  thf('25', plain,
% 10.81/11.00      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 10.81/11.00      inference('simplify', [status(thm)], ['24'])).
% 10.81/11.00  thf('26', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 10.81/11.00      inference('sup+', [status(thm)], ['23', '25'])).
% 10.81/11.00  thf('27', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('28', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 10.81/11.00      inference('sup+', [status(thm)], ['26', '27'])).
% 10.81/11.00  thf('29', plain,
% 10.81/11.00      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 10.81/11.00      inference('simplify', [status(thm)], ['24'])).
% 10.81/11.00  thf(cc2_relset_1, axiom,
% 10.81/11.00    (![A:$i,B:$i,C:$i]:
% 10.81/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.81/11.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 10.81/11.00  thf('30', plain,
% 10.81/11.00      (![X27 : $i, X28 : $i, X29 : $i]:
% 10.81/11.00         ((v4_relat_1 @ X27 @ X28)
% 10.81/11.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 10.81/11.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.81/11.00  thf('31', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | (v4_relat_1 @ X1 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['29', '30'])).
% 10.81/11.00  thf('32', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ sk_B_1 @ X1) | (v4_relat_1 @ sk_D @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['28', '31'])).
% 10.81/11.00  thf('33', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.81/11.00  thf(zf_stmt_3, axiom,
% 10.81/11.00    (![C:$i,B:$i,A:$i]:
% 10.81/11.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.81/11.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.81/11.00  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 10.81/11.00  thf(zf_stmt_5, axiom,
% 10.81/11.00    (![A:$i,B:$i,C:$i]:
% 10.81/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.81/11.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.81/11.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.81/11.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.81/11.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.81/11.00  thf('34', plain,
% 10.81/11.00      (![X46 : $i, X47 : $i, X48 : $i]:
% 10.81/11.00         (~ (zip_tseitin_0 @ X46 @ X47)
% 10.81/11.00          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 10.81/11.00          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.81/11.00  thf('35', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['33', '34'])).
% 10.81/11.00  thf('36', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v4_relat_1 @ sk_D @ X0) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['32', '35'])).
% 10.81/11.00  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('38', plain,
% 10.81/11.00      (![X43 : $i, X44 : $i, X45 : $i]:
% 10.81/11.00         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 10.81/11.00          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 10.81/11.00          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.81/11.00  thf('39', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['37', '38'])).
% 10.81/11.00  thf('40', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf(redefinition_k1_relset_1, axiom,
% 10.81/11.00    (![A:$i,B:$i,C:$i]:
% 10.81/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.81/11.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.81/11.00  thf('41', plain,
% 10.81/11.00      (![X30 : $i, X31 : $i, X32 : $i]:
% 10.81/11.00         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 10.81/11.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 10.81/11.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.81/11.00  thf('42', plain,
% 10.81/11.00      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 10.81/11.00      inference('sup-', [status(thm)], ['40', '41'])).
% 10.81/11.00  thf('43', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('demod', [status(thm)], ['39', '42'])).
% 10.81/11.00  thf('44', plain,
% 10.81/11.00      (![X0 : $i]: ((v4_relat_1 @ sk_D @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['36', '43'])).
% 10.81/11.00  thf(d18_relat_1, axiom,
% 10.81/11.00    (![A:$i,B:$i]:
% 10.81/11.00     ( ( v1_relat_1 @ B ) =>
% 10.81/11.00       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 10.81/11.00  thf('45', plain,
% 10.81/11.00      (![X18 : $i, X19 : $i]:
% 10.81/11.00         (~ (v4_relat_1 @ X18 @ X19)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 10.81/11.00          | ~ (v1_relat_1 @ X18))),
% 10.81/11.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.81/11.00  thf('46', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_D))
% 10.81/11.00          | ~ (v1_relat_1 @ sk_D)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['44', '45'])).
% 10.81/11.00  thf('47', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf(cc1_relset_1, axiom,
% 10.81/11.00    (![A:$i,B:$i,C:$i]:
% 10.81/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.81/11.00       ( v1_relat_1 @ C ) ))).
% 10.81/11.00  thf('48', plain,
% 10.81/11.00      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.81/11.00         ((v1_relat_1 @ X24)
% 10.81/11.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 10.81/11.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.81/11.00  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 10.81/11.00      inference('sup-', [status(thm)], ['47', '48'])).
% 10.81/11.00  thf('50', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_D))
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 10.81/11.00      inference('demod', [status(thm)], ['46', '49'])).
% 10.81/11.00  thf('51', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 10.81/11.00      inference('sup+', [status(thm)], ['23', '25'])).
% 10.81/11.00  thf('52', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('53', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 10.81/11.00      inference('sup+', [status(thm)], ['51', '52'])).
% 10.81/11.00  thf('54', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | (v4_relat_1 @ X1 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['29', '30'])).
% 10.81/11.00  thf('55', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ sk_B_1 @ X1) | (v4_relat_1 @ sk_C_2 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['53', '54'])).
% 10.81/11.00  thf('56', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['33', '34'])).
% 10.81/11.00  thf('57', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v4_relat_1 @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['55', '56'])).
% 10.81/11.00  thf('58', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('demod', [status(thm)], ['39', '42'])).
% 10.81/11.00  thf('59', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v4_relat_1 @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['57', '58'])).
% 10.81/11.00  thf('60', plain,
% 10.81/11.00      (![X18 : $i, X19 : $i]:
% 10.81/11.00         (~ (v4_relat_1 @ X18 @ X19)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 10.81/11.00          | ~ (v1_relat_1 @ X18))),
% 10.81/11.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.81/11.00  thf('61', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_D))
% 10.81/11.00          | ~ (v1_relat_1 @ sk_C_2)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['59', '60'])).
% 10.81/11.00  thf('62', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('63', plain,
% 10.81/11.00      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.81/11.00         ((v1_relat_1 @ X24)
% 10.81/11.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 10.81/11.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.81/11.00  thf('64', plain, ((v1_relat_1 @ sk_C_2)),
% 10.81/11.00      inference('sup-', [status(thm)], ['62', '63'])).
% 10.81/11.00  thf('65', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_D))
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0))),
% 10.81/11.00      inference('demod', [status(thm)], ['61', '64'])).
% 10.81/11.00  thf('66', plain,
% 10.81/11.00      (![X7 : $i, X9 : $i]:
% 10.81/11.00         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 10.81/11.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.81/11.00  thf('67', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_D))
% 10.81/11.00          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ((X0) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['65', '66'])).
% 10.81/11.00  thf('68', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_D))
% 10.81/11.00        | ((k1_relat_1 @ sk_D) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['50', '67'])).
% 10.81/11.00  thf('69', plain,
% 10.81/11.00      ((((k1_relat_1 @ sk_D) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['68'])).
% 10.81/11.00  thf('70', plain,
% 10.81/11.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf('71', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 10.81/11.00      inference('sup+', [status(thm)], ['23', '25'])).
% 10.81/11.00  thf('72', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['33', '34'])).
% 10.81/11.00  thf('73', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 10.81/11.00          | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['71', '72'])).
% 10.81/11.00  thf('74', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('demod', [status(thm)], ['39', '42'])).
% 10.81/11.00  thf('75', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 10.81/11.00          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['73', '74'])).
% 10.81/11.00  thf('76', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('77', plain,
% 10.81/11.00      (((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('sup+', [status(thm)], ['75', '76'])).
% 10.81/11.00  thf('78', plain,
% 10.81/11.00      (![X12 : $i, X13 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 10.81/11.00          | ((X12) != (k1_xboole_0)))),
% 10.81/11.00      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.81/11.00  thf('79', plain,
% 10.81/11.00      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 10.81/11.00      inference('simplify', [status(thm)], ['78'])).
% 10.81/11.00  thf('80', plain,
% 10.81/11.00      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 10.81/11.00         ((r2_hidden @ (sk_E @ X37 @ X38 @ X39) @ X38)
% 10.81/11.00          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 10.81/11.00          | ~ (r2_hidden @ X39 @ X40))),
% 10.81/11.00      inference('cnf', [status(esa)], [t6_relset_1])).
% 10.81/11.00  thf('81', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | ~ (r2_hidden @ X2 @ X1)
% 10.81/11.00          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ X2) @ k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['79', '80'])).
% 10.81/11.00  thf('82', plain,
% 10.81/11.00      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.81/11.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.81/11.00  thf('83', plain,
% 10.81/11.00      (![X27 : $i, X28 : $i, X29 : $i]:
% 10.81/11.00         ((v4_relat_1 @ X27 @ X28)
% 10.81/11.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 10.81/11.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.81/11.00  thf('84', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 10.81/11.00      inference('sup-', [status(thm)], ['82', '83'])).
% 10.81/11.00  thf('85', plain,
% 10.81/11.00      (![X18 : $i, X19 : $i]:
% 10.81/11.00         (~ (v4_relat_1 @ X18 @ X19)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 10.81/11.00          | ~ (v1_relat_1 @ X18))),
% 10.81/11.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.81/11.00  thf('86', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (~ (v1_relat_1 @ k1_xboole_0)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['84', '85'])).
% 10.81/11.00  thf('87', plain,
% 10.81/11.00      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.81/11.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.81/11.00  thf('88', plain,
% 10.81/11.00      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.81/11.00         ((v1_relat_1 @ X24)
% 10.81/11.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 10.81/11.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.81/11.00  thf('89', plain, ((v1_relat_1 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['87', '88'])).
% 10.81/11.00  thf('90', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 10.81/11.00      inference('demod', [status(thm)], ['86', '89'])).
% 10.81/11.00  thf('91', plain,
% 10.81/11.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['3', '4'])).
% 10.81/11.00  thf('92', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['90', '91'])).
% 10.81/11.00  thf('93', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['2', '5'])).
% 10.81/11.00  thf('94', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['90', '91'])).
% 10.81/11.00  thf('95', plain,
% 10.81/11.00      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup+', [status(thm)], ['93', '94'])).
% 10.81/11.00  thf('96', plain,
% 10.81/11.00      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.81/11.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.81/11.00  thf('97', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['2', '5'])).
% 10.81/11.00  thf('98', plain,
% 10.81/11.00      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 10.81/11.00      inference('simplify', [status(thm)], ['78'])).
% 10.81/11.00  thf('99', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup+', [status(thm)], ['97', '98'])).
% 10.81/11.00  thf('100', plain,
% 10.81/11.00      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 10.81/11.00         ((r2_hidden @ (sk_E @ X37 @ X38 @ X39) @ X38)
% 10.81/11.00          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 10.81/11.00          | ~ (r2_hidden @ X39 @ X40))),
% 10.81/11.00      inference('cnf', [status(esa)], [t6_relset_1])).
% 10.81/11.00  thf('101', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | ~ (v1_xboole_0 @ X1)
% 10.81/11.00          | ~ (r2_hidden @ X3 @ X2)
% 10.81/11.00          | (r2_hidden @ (sk_E @ X0 @ X1 @ X3) @ X1))),
% 10.81/11.00      inference('sup-', [status(thm)], ['99', '100'])).
% 10.81/11.00  thf('102', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         ((r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X0)
% 10.81/11.00          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 10.81/11.00          | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['96', '101'])).
% 10.81/11.00  thf('103', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf('104', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 10.81/11.00      inference('clc', [status(thm)], ['102', '103'])).
% 10.81/11.00  thf('105', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 10.81/11.00          | ~ (v1_xboole_0 @ X0)
% 10.81/11.00          | ~ (v1_xboole_0 @ X2))),
% 10.81/11.00      inference('sup-', [status(thm)], ['95', '104'])).
% 10.81/11.00  thf('106', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('condensation', [status(thm)], ['105'])).
% 10.81/11.00  thf('107', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['92', '106'])).
% 10.81/11.00  thf('108', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 10.81/11.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.81/11.00  thf('109', plain,
% 10.81/11.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf(t7_ordinal1, axiom,
% 10.81/11.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.81/11.00  thf('110', plain,
% 10.81/11.00      (![X22 : $i, X23 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 10.81/11.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 10.81/11.00  thf('111', plain,
% 10.81/11.00      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['109', '110'])).
% 10.81/11.00  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['108', '111'])).
% 10.81/11.00  thf('113', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 10.81/11.00      inference('demod', [status(thm)], ['107', '112'])).
% 10.81/11.00  thf('114', plain,
% 10.81/11.00      (![X1 : $i, X2 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X2 @ X1)
% 10.81/11.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 10.81/11.00      inference('clc', [status(thm)], ['81', '113'])).
% 10.81/11.00  thf('115', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_D)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 10.81/11.00      inference('sup-', [status(thm)], ['77', '114'])).
% 10.81/11.00  thf('116', plain,
% 10.81/11.00      (((v1_xboole_0 @ sk_C_2) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['70', '115'])).
% 10.81/11.00  thf('117', plain,
% 10.81/11.00      (![X41 : $i, X42 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.81/11.00  thf('118', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 10.81/11.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.81/11.00  thf('119', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 10.81/11.00      inference('sup+', [status(thm)], ['117', '118'])).
% 10.81/11.00  thf('120', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('121', plain,
% 10.81/11.00      (![X46 : $i, X47 : $i, X48 : $i]:
% 10.81/11.00         (~ (zip_tseitin_0 @ X46 @ X47)
% 10.81/11.00          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 10.81/11.00          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.81/11.00  thf('122', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['120', '121'])).
% 10.81/11.00  thf('123', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((r1_tarski @ sk_B_1 @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['119', '122'])).
% 10.81/11.00  thf('124', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('125', plain,
% 10.81/11.00      (![X43 : $i, X44 : $i, X45 : $i]:
% 10.81/11.00         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 10.81/11.00          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 10.81/11.00          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.81/11.00  thf('126', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['124', '125'])).
% 10.81/11.00  thf('127', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('128', plain,
% 10.81/11.00      (![X30 : $i, X31 : $i, X32 : $i]:
% 10.81/11.00         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 10.81/11.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 10.81/11.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.81/11.00  thf('129', plain,
% 10.81/11.00      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 10.81/11.00      inference('sup-', [status(thm)], ['127', '128'])).
% 10.81/11.00  thf('130', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('demod', [status(thm)], ['126', '129'])).
% 10.81/11.00  thf('131', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((r1_tarski @ sk_B_1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['123', '130'])).
% 10.81/11.00  thf('132', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['0', '1'])).
% 10.81/11.00  thf('133', plain,
% 10.81/11.00      (![X7 : $i, X9 : $i]:
% 10.81/11.00         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 10.81/11.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.81/11.00  thf('134', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['132', '133'])).
% 10.81/11.00  thf('135', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ((sk_B_1) = (X0))
% 10.81/11.00          | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['131', '134'])).
% 10.81/11.00  thf('136', plain,
% 10.81/11.00      (![X41 : $i, X42 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.81/11.00  thf('137', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['90', '91'])).
% 10.81/11.00  thf('138', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (((k1_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 10.81/11.00      inference('sup+', [status(thm)], ['136', '137'])).
% 10.81/11.00  thf('139', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['108', '111'])).
% 10.81/11.00  thf('140', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((v1_xboole_0 @ (k1_relat_1 @ X0)) | (zip_tseitin_0 @ X0 @ X1))),
% 10.81/11.00      inference('sup+', [status(thm)], ['138', '139'])).
% 10.81/11.00  thf('141', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['120', '121'])).
% 10.81/11.00  thf('142', plain,
% 10.81/11.00      (((v1_xboole_0 @ (k1_relat_1 @ sk_B_1))
% 10.81/11.00        | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['140', '141'])).
% 10.81/11.00  thf('143', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('demod', [status(thm)], ['126', '129'])).
% 10.81/11.00  thf('144', plain,
% 10.81/11.00      (((v1_xboole_0 @ (k1_relat_1 @ sk_B_1))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['142', '143'])).
% 10.81/11.00  thf('145', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 10.81/11.00      inference('sup+', [status(thm)], ['26', '27'])).
% 10.81/11.00  thf('146', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['2', '5'])).
% 10.81/11.00  thf('147', plain,
% 10.81/11.00      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 10.81/11.00      inference('simplify', [status(thm)], ['78'])).
% 10.81/11.00  thf('148', plain,
% 10.81/11.00      (![X27 : $i, X28 : $i, X29 : $i]:
% 10.81/11.00         ((v4_relat_1 @ X27 @ X28)
% 10.81/11.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 10.81/11.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.81/11.00  thf('149', plain,
% 10.81/11.00      (![X1 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | (v4_relat_1 @ X1 @ k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['147', '148'])).
% 10.81/11.00  thf('150', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 10.81/11.00          | ~ (v1_xboole_0 @ X0)
% 10.81/11.00          | (v4_relat_1 @ X1 @ k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['146', '149'])).
% 10.81/11.00  thf('151', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 10.81/11.00          | (v4_relat_1 @ sk_D @ k1_xboole_0)
% 10.81/11.00          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['145', '150'])).
% 10.81/11.00  thf('152', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['108', '111'])).
% 10.81/11.00  thf('153', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ sk_B_1 @ X0) | (v4_relat_1 @ sk_D @ k1_xboole_0))),
% 10.81/11.00      inference('demod', [status(thm)], ['151', '152'])).
% 10.81/11.00  thf('154', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['120', '121'])).
% 10.81/11.00  thf('155', plain,
% 10.81/11.00      (((v4_relat_1 @ sk_D @ k1_xboole_0)
% 10.81/11.00        | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['153', '154'])).
% 10.81/11.00  thf('156', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('demod', [status(thm)], ['126', '129'])).
% 10.81/11.00  thf('157', plain,
% 10.81/11.00      (((v4_relat_1 @ sk_D @ k1_xboole_0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['155', '156'])).
% 10.81/11.00  thf('158', plain,
% 10.81/11.00      (![X18 : $i, X19 : $i]:
% 10.81/11.00         (~ (v4_relat_1 @ X18 @ X19)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 10.81/11.00          | ~ (v1_relat_1 @ X18))),
% 10.81/11.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.81/11.00  thf('159', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ~ (v1_relat_1 @ sk_D)
% 10.81/11.00        | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['157', '158'])).
% 10.81/11.00  thf('160', plain, ((v1_relat_1 @ sk_D)),
% 10.81/11.00      inference('sup-', [status(thm)], ['47', '48'])).
% 10.81/11.00  thf('161', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | (r1_tarski @ (k1_relat_1 @ sk_D) @ k1_xboole_0))),
% 10.81/11.00      inference('demod', [status(thm)], ['159', '160'])).
% 10.81/11.00  thf('162', plain,
% 10.81/11.00      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['3', '4'])).
% 10.81/11.00  thf('163', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['161', '162'])).
% 10.81/11.00  thf('164', plain,
% 10.81/11.00      (![X18 : $i, X19 : $i]:
% 10.81/11.00         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 10.81/11.00          | (v4_relat_1 @ X18 @ X19)
% 10.81/11.00          | ~ (v1_relat_1 @ X18))),
% 10.81/11.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.81/11.00  thf('165', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 10.81/11.00          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ~ (v1_relat_1 @ sk_D)
% 10.81/11.00          | (v4_relat_1 @ sk_D @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['163', '164'])).
% 10.81/11.00  thf('166', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 10.81/11.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.81/11.00  thf('167', plain, ((v1_relat_1 @ sk_D)),
% 10.81/11.00      inference('sup-', [status(thm)], ['47', '48'])).
% 10.81/11.00  thf('168', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2)) | (v4_relat_1 @ sk_D @ X0))),
% 10.81/11.00      inference('demod', [status(thm)], ['165', '166', '167'])).
% 10.81/11.00  thf('169', plain,
% 10.81/11.00      (![X18 : $i, X19 : $i]:
% 10.81/11.00         (~ (v4_relat_1 @ X18 @ X19)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 10.81/11.00          | ~ (v1_relat_1 @ X18))),
% 10.81/11.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.81/11.00  thf('170', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ~ (v1_relat_1 @ sk_D)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['168', '169'])).
% 10.81/11.00  thf('171', plain, ((v1_relat_1 @ sk_D)),
% 10.81/11.00      inference('sup-', [status(thm)], ['47', '48'])).
% 10.81/11.00  thf('172', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 10.81/11.00      inference('demod', [status(thm)], ['170', '171'])).
% 10.81/11.00  thf('173', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['132', '133'])).
% 10.81/11.00  thf('174', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ((k1_relat_1 @ sk_D) = (X0))
% 10.81/11.00          | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['172', '173'])).
% 10.81/11.00  thf('175', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((k1_relat_1 @ sk_D) = (k1_relat_1 @ sk_B_1))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['144', '174'])).
% 10.81/11.00  thf('176', plain,
% 10.81/11.00      ((((k1_relat_1 @ sk_D) = (k1_relat_1 @ sk_B_1))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['175'])).
% 10.81/11.00  thf('177', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ sk_B_1 @ X1) | (v4_relat_1 @ sk_C_2 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['53', '54'])).
% 10.81/11.00  thf('178', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['120', '121'])).
% 10.81/11.00  thf('179', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v4_relat_1 @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['177', '178'])).
% 10.81/11.00  thf('180', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('demod', [status(thm)], ['126', '129'])).
% 10.81/11.00  thf('181', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v4_relat_1 @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['179', '180'])).
% 10.81/11.00  thf('182', plain,
% 10.81/11.00      (![X18 : $i, X19 : $i]:
% 10.81/11.00         (~ (v4_relat_1 @ X18 @ X19)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 10.81/11.00          | ~ (v1_relat_1 @ X18))),
% 10.81/11.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.81/11.00  thf('183', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ~ (v1_relat_1 @ sk_C_2)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['181', '182'])).
% 10.81/11.00  thf('184', plain, ((v1_relat_1 @ sk_C_2)),
% 10.81/11.00      inference('sup-', [status(thm)], ['62', '63'])).
% 10.81/11.00  thf('185', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0))),
% 10.81/11.00      inference('demod', [status(thm)], ['183', '184'])).
% 10.81/11.00  thf('186', plain,
% 10.81/11.00      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['109', '110'])).
% 10.81/11.00  thf('187', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | (v1_xboole_0 @ (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['185', '186'])).
% 10.81/11.00  thf('188', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ((k1_relat_1 @ sk_D) = (X0))
% 10.81/11.00          | ~ (v1_xboole_0 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['172', '173'])).
% 10.81/11.00  thf('189', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((k1_relat_1 @ sk_D) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['187', '188'])).
% 10.81/11.00  thf('190', plain,
% 10.81/11.00      ((((k1_relat_1 @ sk_D) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['189'])).
% 10.81/11.00  thf('191', plain,
% 10.81/11.00      ((((k1_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup+', [status(thm)], ['176', '190'])).
% 10.81/11.00  thf('192', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((k1_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['191'])).
% 10.81/11.00  thf('193', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('194', plain,
% 10.81/11.00      (![X27 : $i, X28 : $i, X29 : $i]:
% 10.81/11.00         ((v4_relat_1 @ X27 @ X28)
% 10.81/11.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 10.81/11.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.81/11.00  thf('195', plain, ((v4_relat_1 @ sk_C_2 @ sk_A)),
% 10.81/11.00      inference('sup-', [status(thm)], ['193', '194'])).
% 10.81/11.00  thf('196', plain,
% 10.81/11.00      (![X18 : $i, X19 : $i]:
% 10.81/11.00         (~ (v4_relat_1 @ X18 @ X19)
% 10.81/11.00          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 10.81/11.00          | ~ (v1_relat_1 @ X18))),
% 10.81/11.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.81/11.00  thf('197', plain,
% 10.81/11.00      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['195', '196'])).
% 10.81/11.00  thf('198', plain, ((v1_relat_1 @ sk_C_2)),
% 10.81/11.00      inference('sup-', [status(thm)], ['62', '63'])).
% 10.81/11.00  thf('199', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 10.81/11.00      inference('demod', [status(thm)], ['197', '198'])).
% 10.81/11.00  thf('200', plain,
% 10.81/11.00      (![X7 : $i, X9 : $i]:
% 10.81/11.00         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 10.81/11.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.81/11.00  thf('201', plain,
% 10.81/11.00      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['199', '200'])).
% 10.81/11.00  thf('202', plain,
% 10.81/11.00      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_1))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['192', '201'])).
% 10.81/11.00  thf('203', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00        | ~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['202'])).
% 10.81/11.00  thf('204', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (~ (r1_tarski @ sk_A @ (k1_relat_1 @ X0))
% 10.81/11.00          | ~ (v1_xboole_0 @ X0)
% 10.81/11.00          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['135', '203'])).
% 10.81/11.00  thf('205', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ~ (v1_xboole_0 @ X0)
% 10.81/11.00          | ~ (r1_tarski @ sk_A @ (k1_relat_1 @ X0)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['204'])).
% 10.81/11.00  thf('206', plain,
% 10.81/11.00      ((~ (r1_tarski @ sk_A @ sk_A)
% 10.81/11.00        | (v1_xboole_0 @ sk_C_2)
% 10.81/11.00        | ~ (v1_xboole_0 @ sk_D)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['116', '205'])).
% 10.81/11.00  thf('207', plain,
% 10.81/11.00      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 10.81/11.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.81/11.00  thf('208', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 10.81/11.00      inference('simplify', [status(thm)], ['207'])).
% 10.81/11.00  thf('209', plain,
% 10.81/11.00      (((v1_xboole_0 @ sk_C_2)
% 10.81/11.00        | ~ (v1_xboole_0 @ sk_D)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('demod', [status(thm)], ['206', '208'])).
% 10.81/11.00  thf('210', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 10.81/11.00      inference('sup-', [status(thm)], ['13', '14'])).
% 10.81/11.00  thf('211', plain,
% 10.81/11.00      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_D))),
% 10.81/11.00      inference('clc', [status(thm)], ['209', '210'])).
% 10.81/11.00  thf('212', plain,
% 10.81/11.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf('213', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 10.81/11.00      inference('sup+', [status(thm)], ['23', '25'])).
% 10.81/11.00  thf('214', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['120', '121'])).
% 10.81/11.00  thf('215', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 10.81/11.00          | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['213', '214'])).
% 10.81/11.00  thf('216', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('demod', [status(thm)], ['126', '129'])).
% 10.81/11.00  thf('217', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 10.81/11.00          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['215', '216'])).
% 10.81/11.00  thf('218', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('219', plain,
% 10.81/11.00      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup+', [status(thm)], ['217', '218'])).
% 10.81/11.00  thf('220', plain,
% 10.81/11.00      (![X1 : $i, X2 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X2 @ X1)
% 10.81/11.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 10.81/11.00      inference('clc', [status(thm)], ['81', '113'])).
% 10.81/11.00  thf('221', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) = (k1_relat_1 @ sk_C_2)) | ~ (r2_hidden @ X0 @ sk_D))),
% 10.81/11.00      inference('sup-', [status(thm)], ['219', '220'])).
% 10.81/11.00  thf('222', plain,
% 10.81/11.00      (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['212', '221'])).
% 10.81/11.00  thf('223', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 10.81/11.00      inference('clc', [status(thm)], ['211', '222'])).
% 10.81/11.00  thf('224', plain,
% 10.81/11.00      ((((k1_relat_1 @ sk_D) = (sk_A)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.81/11.00      inference('demod', [status(thm)], ['69', '223'])).
% 10.81/11.00  thf('225', plain, (((k1_relat_1 @ sk_D) = (sk_A))),
% 10.81/11.00      inference('simplify', [status(thm)], ['224'])).
% 10.81/11.00  thf('226', plain,
% 10.81/11.00      (![X41 : $i, X42 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.81/11.00  thf('227', plain,
% 10.81/11.00      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['120', '121'])).
% 10.81/11.00  thf('228', plain,
% 10.81/11.00      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 10.81/11.00      inference('sup-', [status(thm)], ['226', '227'])).
% 10.81/11.00  thf('229', plain,
% 10.81/11.00      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 10.81/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('demod', [status(thm)], ['126', '129'])).
% 10.81/11.00  thf('230', plain,
% 10.81/11.00      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['228', '229'])).
% 10.81/11.00  thf(t9_funct_1, axiom,
% 10.81/11.00    (![A:$i]:
% 10.81/11.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.81/11.00       ( ![B:$i]:
% 10.81/11.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 10.81/11.00           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 10.81/11.00               ( ![C:$i]:
% 10.81/11.00                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 10.81/11.00                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 10.81/11.00             ( ( A ) = ( B ) ) ) ) ) ))).
% 10.81/11.00  thf('231', plain,
% 10.81/11.00      (![X20 : $i, X21 : $i]:
% 10.81/11.00         (~ (v1_relat_1 @ X20)
% 10.81/11.00          | ~ (v1_funct_1 @ X20)
% 10.81/11.00          | ((X21) = (X20))
% 10.81/11.00          | (r2_hidden @ (sk_C_1 @ X20 @ X21) @ (k1_relat_1 @ X21))
% 10.81/11.00          | ((k1_relat_1 @ X21) != (k1_relat_1 @ X20))
% 10.81/11.00          | ~ (v1_funct_1 @ X21)
% 10.81/11.00          | ~ (v1_relat_1 @ X21))),
% 10.81/11.00      inference('cnf', [status(esa)], [t9_funct_1])).
% 10.81/11.00  thf('232', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) != (k1_relat_1 @ X0))
% 10.81/11.00          | ((sk_B_1) = (k1_xboole_0))
% 10.81/11.00          | ~ (v1_relat_1 @ sk_C_2)
% 10.81/11.00          | ~ (v1_funct_1 @ sk_C_2)
% 10.81/11.00          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ((sk_C_2) = (X0))
% 10.81/11.00          | ~ (v1_funct_1 @ X0)
% 10.81/11.00          | ~ (v1_relat_1 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['230', '231'])).
% 10.81/11.00  thf('233', plain, ((v1_relat_1 @ sk_C_2)),
% 10.81/11.00      inference('sup-', [status(thm)], ['62', '63'])).
% 10.81/11.00  thf('234', plain, ((v1_funct_1 @ sk_C_2)),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('235', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) != (k1_relat_1 @ X0))
% 10.81/11.00          | ((sk_B_1) = (k1_xboole_0))
% 10.81/11.00          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.81/11.00          | ((sk_C_2) = (X0))
% 10.81/11.00          | ~ (v1_funct_1 @ X0)
% 10.81/11.00          | ~ (v1_relat_1 @ X0))),
% 10.81/11.00      inference('demod', [status(thm)], ['232', '233', '234'])).
% 10.81/11.00  thf('236', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 10.81/11.00      inference('clc', [status(thm)], ['211', '222'])).
% 10.81/11.00  thf('237', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((sk_A) != (k1_relat_1 @ X0))
% 10.81/11.00          | ((sk_B_1) = (k1_xboole_0))
% 10.81/11.00          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 10.81/11.00          | ((sk_C_2) = (X0))
% 10.81/11.00          | ~ (v1_funct_1 @ X0)
% 10.81/11.00          | ~ (v1_relat_1 @ X0))),
% 10.81/11.00      inference('demod', [status(thm)], ['235', '236'])).
% 10.81/11.00  thf('238', plain,
% 10.81/11.00      ((((sk_A) != (sk_A))
% 10.81/11.00        | ~ (v1_relat_1 @ sk_D)
% 10.81/11.00        | ~ (v1_funct_1 @ sk_D)
% 10.81/11.00        | ((sk_C_2) = (sk_D))
% 10.81/11.00        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A)
% 10.81/11.00        | ((sk_B_1) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['225', '237'])).
% 10.81/11.00  thf('239', plain, ((v1_relat_1 @ sk_D)),
% 10.81/11.00      inference('sup-', [status(thm)], ['47', '48'])).
% 10.81/11.00  thf('240', plain, ((v1_funct_1 @ sk_D)),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('241', plain,
% 10.81/11.00      ((((sk_A) != (sk_A))
% 10.81/11.00        | ((sk_C_2) = (sk_D))
% 10.81/11.00        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A)
% 10.81/11.00        | ((sk_B_1) = (k1_xboole_0)))),
% 10.81/11.00      inference('demod', [status(thm)], ['238', '239', '240'])).
% 10.81/11.00  thf('242', plain,
% 10.81/11.00      ((((sk_B_1) = (k1_xboole_0))
% 10.81/11.00        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A)
% 10.81/11.00        | ((sk_C_2) = (sk_D)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['241'])).
% 10.81/11.00  thf('243', plain,
% 10.81/11.00      (![X49 : $i]:
% 10.81/11.00         (((k1_funct_1 @ sk_C_2 @ X49) = (k1_funct_1 @ sk_D @ X49))
% 10.81/11.00          | ~ (r2_hidden @ X49 @ sk_A))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('244', plain,
% 10.81/11.00      ((((sk_C_2) = (sk_D))
% 10.81/11.00        | ((sk_B_1) = (k1_xboole_0))
% 10.81/11.00        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.81/11.00            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 10.81/11.00      inference('sup-', [status(thm)], ['242', '243'])).
% 10.81/11.00  thf('245', plain,
% 10.81/11.00      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.81/11.00          = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.81/11.00        | ((sk_B_1) = (k1_xboole_0)))),
% 10.81/11.00      inference('condensation', [status(thm)], ['244'])).
% 10.81/11.00  thf('246', plain,
% 10.81/11.00      (![X20 : $i, X21 : $i]:
% 10.81/11.00         (~ (v1_relat_1 @ X20)
% 10.81/11.00          | ~ (v1_funct_1 @ X20)
% 10.81/11.00          | ((X21) = (X20))
% 10.81/11.00          | ((k1_funct_1 @ X21 @ (sk_C_1 @ X20 @ X21))
% 10.81/11.00              != (k1_funct_1 @ X20 @ (sk_C_1 @ X20 @ X21)))
% 10.81/11.00          | ((k1_relat_1 @ X21) != (k1_relat_1 @ X20))
% 10.81/11.00          | ~ (v1_funct_1 @ X21)
% 10.81/11.00          | ~ (v1_relat_1 @ X21))),
% 10.81/11.00      inference('cnf', [status(esa)], [t9_funct_1])).
% 10.81/11.00  thf('247', plain,
% 10.81/11.00      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.81/11.00          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.81/11.00        | ((sk_B_1) = (k1_xboole_0))
% 10.81/11.00        | ~ (v1_relat_1 @ sk_C_2)
% 10.81/11.00        | ~ (v1_funct_1 @ sk_C_2)
% 10.81/11.00        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 10.81/11.00        | ((sk_C_2) = (sk_D))
% 10.81/11.00        | ~ (v1_funct_1 @ sk_D)
% 10.81/11.00        | ~ (v1_relat_1 @ sk_D))),
% 10.81/11.00      inference('sup-', [status(thm)], ['245', '246'])).
% 10.81/11.00  thf('248', plain, ((v1_relat_1 @ sk_C_2)),
% 10.81/11.00      inference('sup-', [status(thm)], ['62', '63'])).
% 10.81/11.00  thf('249', plain, ((v1_funct_1 @ sk_C_2)),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('250', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 10.81/11.00      inference('clc', [status(thm)], ['211', '222'])).
% 10.81/11.00  thf('251', plain, (((k1_relat_1 @ sk_D) = (sk_A))),
% 10.81/11.00      inference('simplify', [status(thm)], ['224'])).
% 10.81/11.00  thf('252', plain, ((v1_funct_1 @ sk_D)),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('253', plain, ((v1_relat_1 @ sk_D)),
% 10.81/11.00      inference('sup-', [status(thm)], ['47', '48'])).
% 10.81/11.00  thf('254', plain,
% 10.81/11.00      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.81/11.00          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.81/11.00        | ((sk_B_1) = (k1_xboole_0))
% 10.81/11.00        | ((sk_A) != (sk_A))
% 10.81/11.00        | ((sk_C_2) = (sk_D)))),
% 10.81/11.00      inference('demod', [status(thm)],
% 10.81/11.00                ['247', '248', '249', '250', '251', '252', '253'])).
% 10.81/11.00  thf('255', plain, ((((sk_C_2) = (sk_D)) | ((sk_B_1) = (k1_xboole_0)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['254'])).
% 10.81/11.00  thf('256', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('257', plain,
% 10.81/11.00      ((~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)
% 10.81/11.00        | ((sk_B_1) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['255', '256'])).
% 10.81/11.00  thf('258', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('259', plain,
% 10.81/11.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 10.81/11.00         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 10.81/11.00          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 10.81/11.00      inference('simplify', [status(thm)], ['9'])).
% 10.81/11.00  thf('260', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 10.81/11.00      inference('sup-', [status(thm)], ['258', '259'])).
% 10.81/11.00  thf('261', plain, (((sk_B_1) = (k1_xboole_0))),
% 10.81/11.00      inference('demod', [status(thm)], ['257', '260'])).
% 10.81/11.00  thf('262', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['108', '111'])).
% 10.81/11.00  thf('263', plain, ((v1_xboole_0 @ sk_C_2)),
% 10.81/11.00      inference('demod', [status(thm)], ['22', '261', '262'])).
% 10.81/11.00  thf('264', plain, (~ (v1_xboole_0 @ sk_D)),
% 10.81/11.00      inference('demod', [status(thm)], ['15', '263'])).
% 10.81/11.00  thf('265', plain,
% 10.81/11.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf('266', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.81/11.00          | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 10.81/11.00      inference('sup+', [status(thm)], ['26', '27'])).
% 10.81/11.00  thf('267', plain,
% 10.81/11.00      (![X1 : $i, X2 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X2 @ X1)
% 10.81/11.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 10.81/11.00      inference('clc', [status(thm)], ['81', '113'])).
% 10.81/11.00  thf('268', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_D))),
% 10.81/11.00      inference('sup-', [status(thm)], ['266', '267'])).
% 10.81/11.00  thf('269', plain,
% 10.81/11.00      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['265', '268'])).
% 10.81/11.00  thf('270', plain,
% 10.81/11.00      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.81/11.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.81/11.00  thf('271', plain,
% 10.81/11.00      (![X46 : $i, X47 : $i, X48 : $i]:
% 10.81/11.00         (~ (zip_tseitin_0 @ X46 @ X47)
% 10.81/11.00          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 10.81/11.00          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.81/11.00  thf('272', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 10.81/11.00      inference('sup-', [status(thm)], ['270', '271'])).
% 10.81/11.00  thf('273', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['269', '272'])).
% 10.81/11.00  thf('274', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['2', '5'])).
% 10.81/11.00  thf('275', plain,
% 10.81/11.00      (![X46 : $i, X47 : $i, X48 : $i]:
% 10.81/11.00         (((X46) != (k1_xboole_0))
% 10.81/11.00          | ((X47) = (k1_xboole_0))
% 10.81/11.00          | (v1_funct_2 @ X48 @ X47 @ X46)
% 10.81/11.00          | ((X48) != (k1_xboole_0))
% 10.81/11.00          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.81/11.00  thf('276', plain,
% 10.81/11.00      (![X47 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 10.81/11.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ k1_xboole_0)))
% 10.81/11.00          | (v1_funct_2 @ k1_xboole_0 @ X47 @ k1_xboole_0)
% 10.81/11.00          | ((X47) = (k1_xboole_0)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['275'])).
% 10.81/11.00  thf('277', plain,
% 10.81/11.00      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 10.81/11.00      inference('simplify', [status(thm)], ['24'])).
% 10.81/11.00  thf('278', plain,
% 10.81/11.00      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.81/11.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.81/11.00  thf('279', plain,
% 10.81/11.00      (![X47 : $i]:
% 10.81/11.00         ((v1_funct_2 @ k1_xboole_0 @ X47 @ k1_xboole_0)
% 10.81/11.00          | ((X47) = (k1_xboole_0)))),
% 10.81/11.00      inference('demod', [status(thm)], ['276', '277', '278'])).
% 10.81/11.00  thf('280', plain,
% 10.81/11.00      (![X43 : $i, X44 : $i, X45 : $i]:
% 10.81/11.00         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 10.81/11.00          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 10.81/11.00          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.81/11.00  thf('281', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((X0) = (k1_xboole_0))
% 10.81/11.00          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 10.81/11.00          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['279', '280'])).
% 10.81/11.00  thf('282', plain,
% 10.81/11.00      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.81/11.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.81/11.00  thf('283', plain,
% 10.81/11.00      (![X30 : $i, X31 : $i, X32 : $i]:
% 10.81/11.00         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 10.81/11.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 10.81/11.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.81/11.00  thf('284', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['282', '283'])).
% 10.81/11.00  thf('285', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['90', '91'])).
% 10.81/11.00  thf('286', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 10.81/11.00      inference('demod', [status(thm)], ['284', '285'])).
% 10.81/11.00  thf('287', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (((X0) = (k1_xboole_0))
% 10.81/11.00          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 10.81/11.00          | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('demod', [status(thm)], ['281', '286'])).
% 10.81/11.00  thf('288', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 10.81/11.00          | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('simplify', [status(thm)], ['287'])).
% 10.81/11.00  thf('289', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 10.81/11.00          | ~ (v1_xboole_0 @ X0)
% 10.81/11.00          | ((X1) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['274', '288'])).
% 10.81/11.00  thf('290', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v1_xboole_0 @ sk_D)
% 10.81/11.00          | ((X0) = (k1_xboole_0))
% 10.81/11.00          | ~ (v1_xboole_0 @ sk_B_1))),
% 10.81/11.00      inference('sup-', [status(thm)], ['273', '289'])).
% 10.81/11.00  thf('291', plain,
% 10.81/11.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 10.81/11.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 10.81/11.00  thf('292', plain, (((k1_relat_1 @ sk_D) = (sk_A))),
% 10.81/11.00      inference('simplify', [status(thm)], ['224'])).
% 10.81/11.00  thf('293', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (((k1_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 10.81/11.00      inference('sup+', [status(thm)], ['136', '137'])).
% 10.81/11.00  thf('294', plain,
% 10.81/11.00      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 10.81/11.00      inference('simplify', [status(thm)], ['78'])).
% 10.81/11.00  thf('295', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1) = (k1_xboole_0))
% 10.81/11.00          | (zip_tseitin_0 @ X0 @ X2))),
% 10.81/11.00      inference('sup+', [status(thm)], ['293', '294'])).
% 10.81/11.00  thf('296', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (((k2_zfmisc_1 @ sk_A @ X0) = (k1_xboole_0))
% 10.81/11.00          | (zip_tseitin_0 @ sk_D @ X1))),
% 10.81/11.00      inference('sup+', [status(thm)], ['292', '295'])).
% 10.81/11.00  thf('297', plain,
% 10.81/11.00      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.81/11.00  thf('298', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['2', '5'])).
% 10.81/11.00  thf('299', plain,
% 10.81/11.00      (![X1 : $i, X2 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X2 @ X1)
% 10.81/11.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 10.81/11.00      inference('clc', [status(thm)], ['81', '113'])).
% 10.81/11.00  thf('300', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.81/11.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 10.81/11.00          | ~ (v1_xboole_0 @ X0)
% 10.81/11.00          | ~ (r2_hidden @ X2 @ X1))),
% 10.81/11.00      inference('sup-', [status(thm)], ['298', '299'])).
% 10.81/11.00  thf('301', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         (~ (r2_hidden @ X0 @ sk_C_2)
% 10.81/11.00          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['297', '300'])).
% 10.81/11.00  thf('302', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (v1_xboole_0 @ k1_xboole_0)
% 10.81/11.00          | (zip_tseitin_0 @ sk_D @ X1)
% 10.81/11.00          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 10.81/11.00      inference('sup-', [status(thm)], ['296', '301'])).
% 10.81/11.00  thf('303', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['108', '111'])).
% 10.81/11.00  thf('304', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((zip_tseitin_0 @ sk_D @ X1) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 10.81/11.00      inference('demod', [status(thm)], ['302', '303'])).
% 10.81/11.00  thf('305', plain,
% 10.81/11.00      (![X0 : $i]: ((v1_xboole_0 @ sk_C_2) | (zip_tseitin_0 @ sk_D @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['291', '304'])).
% 10.81/11.00  thf('306', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 10.81/11.00      inference('sup-', [status(thm)], ['270', '271'])).
% 10.81/11.00  thf('307', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v1_xboole_0 @ sk_C_2) | (zip_tseitin_1 @ k1_xboole_0 @ sk_D @ X0))),
% 10.81/11.00      inference('sup-', [status(thm)], ['305', '306'])).
% 10.81/11.00  thf('308', plain,
% 10.81/11.00      (![X0 : $i, X1 : $i]:
% 10.81/11.00         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 10.81/11.00          | ~ (v1_xboole_0 @ X0)
% 10.81/11.00          | ((X1) = (k1_xboole_0)))),
% 10.81/11.00      inference('sup-', [status(thm)], ['274', '288'])).
% 10.81/11.00  thf('309', plain,
% 10.81/11.00      (![X0 : $i]:
% 10.81/11.00         ((v1_xboole_0 @ sk_C_2)
% 10.81/11.00          | ((X0) = (k1_xboole_0))
% 10.81/11.00          | ~ (v1_xboole_0 @ sk_D))),
% 10.81/11.00      inference('sup-', [status(thm)], ['307', '308'])).
% 10.81/11.00  thf('310', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 10.81/11.00      inference('sup-', [status(thm)], ['13', '14'])).
% 10.81/11.00  thf('311', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ sk_D) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('clc', [status(thm)], ['309', '310'])).
% 10.81/11.00  thf('312', plain,
% 10.81/11.00      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ((X0) = (k1_xboole_0)))),
% 10.81/11.00      inference('clc', [status(thm)], ['290', '311'])).
% 10.81/11.00  thf('313', plain, (((sk_B_1) = (k1_xboole_0))),
% 10.81/11.00      inference('demod', [status(thm)], ['257', '260'])).
% 10.81/11.00  thf('314', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['108', '111'])).
% 10.81/11.00  thf('315', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 10.81/11.00      inference('demod', [status(thm)], ['312', '313', '314'])).
% 10.81/11.00  thf('316', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.81/11.00      inference('sup-', [status(thm)], ['108', '111'])).
% 10.81/11.00  thf('317', plain, ($false),
% 10.81/11.00      inference('demod', [status(thm)], ['264', '315', '316'])).
% 10.81/11.00  
% 10.81/11.00  % SZS output end Refutation
% 10.81/11.00  
% 10.81/11.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
