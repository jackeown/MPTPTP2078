%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MIHtFp8b8i

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:39 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 566 expanded)
%              Number of leaves         :   40 ( 192 expanded)
%              Depth                    :   23
%              Number of atoms          :  974 (6597 expanded)
%              Number of equality atoms :   67 ( 266 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
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

thf('14',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( r2_relset_1 @ X38 @ X39 @ X37 @ X40 )
      | ( X37 != X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('30',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_relset_1 @ X38 @ X39 @ X40 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','32'])).

thf('34',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['36','41'])).

thf('43',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','42'])).

thf('44',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['36','41'])).

thf('56',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['51','56'])).

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

thf('58',plain,(
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

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','64','65','66'])).

thf('68',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['68','73','74'])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X49: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X49 )
        = ( k1_funct_1 @ sk_D @ X49 ) )
      | ~ ( r2_hidden @ X49 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['78'])).

thf('80',plain,(
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

thf('81',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['62','63'])).

thf('83',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('85',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','43'])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('88',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['81','82','83','84','85','86','87'])).

thf('89',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_relset_1 @ X38 @ X39 @ X40 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('92',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MIHtFp8b8i
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:53:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.18/2.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.18/2.44  % Solved by: fo/fo7.sh
% 2.18/2.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.18/2.44  % done 2840 iterations in 1.981s
% 2.18/2.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.18/2.44  % SZS output start Refutation
% 2.18/2.44  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.18/2.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.18/2.44  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.18/2.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.18/2.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.18/2.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.18/2.44  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.18/2.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.18/2.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.18/2.44  thf(sk_A_type, type, sk_A: $i).
% 2.18/2.44  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.18/2.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.18/2.44  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.18/2.44  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.18/2.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.18/2.44  thf(sk_D_type, type, sk_D: $i).
% 2.18/2.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.18/2.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.18/2.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.18/2.44  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.18/2.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.18/2.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.18/2.44  thf(t18_funct_2, conjecture,
% 2.18/2.44    (![A:$i,B:$i,C:$i]:
% 2.18/2.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.18/2.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.18/2.44       ( ![D:$i]:
% 2.18/2.44         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.18/2.44             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.18/2.44           ( ( ![E:$i]:
% 2.18/2.44               ( ( r2_hidden @ E @ A ) =>
% 2.18/2.44                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.18/2.44             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 2.18/2.44  thf(zf_stmt_0, negated_conjecture,
% 2.18/2.44    (~( ![A:$i,B:$i,C:$i]:
% 2.18/2.44        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.18/2.44            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.18/2.44          ( ![D:$i]:
% 2.18/2.44            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.18/2.44                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.18/2.44              ( ( ![E:$i]:
% 2.18/2.44                  ( ( r2_hidden @ E @ A ) =>
% 2.18/2.44                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.18/2.44                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 2.18/2.44    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 2.18/2.44  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf(d1_funct_2, axiom,
% 2.18/2.44    (![A:$i,B:$i,C:$i]:
% 2.18/2.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.18/2.44       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.18/2.44           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.18/2.44             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.18/2.44         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.18/2.44           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.18/2.44             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.18/2.44  thf(zf_stmt_1, axiom,
% 2.18/2.44    (![C:$i,B:$i,A:$i]:
% 2.18/2.44     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.18/2.44       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.18/2.44  thf('2', plain,
% 2.18/2.44      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.18/2.44         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 2.18/2.44          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 2.18/2.44          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.18/2.44  thf('3', plain,
% 2.18/2.44      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.18/2.44        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 2.18/2.44      inference('sup-', [status(thm)], ['1', '2'])).
% 2.18/2.44  thf('4', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf(redefinition_k1_relset_1, axiom,
% 2.18/2.44    (![A:$i,B:$i,C:$i]:
% 2.18/2.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.18/2.44       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.18/2.44  thf('5', plain,
% 2.18/2.44      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.18/2.44         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 2.18/2.44          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.18/2.44      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.18/2.44  thf('6', plain,
% 2.18/2.44      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.18/2.44      inference('sup-', [status(thm)], ['4', '5'])).
% 2.18/2.44  thf('7', plain,
% 2.18/2.44      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.18/2.44        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.18/2.44      inference('demod', [status(thm)], ['3', '6'])).
% 2.18/2.44  thf('8', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.18/2.44  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.18/2.44  thf(zf_stmt_4, axiom,
% 2.18/2.44    (![B:$i,A:$i]:
% 2.18/2.44     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.18/2.44       ( zip_tseitin_0 @ B @ A ) ))).
% 2.18/2.44  thf(zf_stmt_5, axiom,
% 2.18/2.44    (![A:$i,B:$i,C:$i]:
% 2.18/2.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.18/2.44       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.18/2.44         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.18/2.44           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.18/2.44             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.18/2.44  thf('9', plain,
% 2.18/2.44      (![X46 : $i, X47 : $i, X48 : $i]:
% 2.18/2.44         (~ (zip_tseitin_0 @ X46 @ X47)
% 2.18/2.44          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 2.18/2.44          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.18/2.44  thf('10', plain,
% 2.18/2.44      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.18/2.44        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.18/2.44      inference('sup-', [status(thm)], ['8', '9'])).
% 2.18/2.44  thf('11', plain,
% 2.18/2.44      (![X41 : $i, X42 : $i]:
% 2.18/2.44         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.18/2.44  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.18/2.44  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.18/2.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.18/2.44  thf('13', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.18/2.44      inference('sup+', [status(thm)], ['11', '12'])).
% 2.18/2.44  thf('14', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf(cc4_relset_1, axiom,
% 2.18/2.44    (![A:$i,B:$i]:
% 2.18/2.44     ( ( v1_xboole_0 @ A ) =>
% 2.18/2.44       ( ![C:$i]:
% 2.18/2.44         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.18/2.44           ( v1_xboole_0 @ C ) ) ) ))).
% 2.18/2.44  thf('15', plain,
% 2.18/2.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.18/2.44         (~ (v1_xboole_0 @ X31)
% 2.18/2.44          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 2.18/2.44          | (v1_xboole_0 @ X32))),
% 2.18/2.44      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.18/2.44  thf('16', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 2.18/2.44      inference('sup-', [status(thm)], ['14', '15'])).
% 2.18/2.44  thf('17', plain,
% 2.18/2.44      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 2.18/2.44      inference('sup-', [status(thm)], ['13', '16'])).
% 2.18/2.44  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.18/2.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.18/2.44  thf(d3_tarski, axiom,
% 2.18/2.44    (![A:$i,B:$i]:
% 2.18/2.44     ( ( r1_tarski @ A @ B ) <=>
% 2.18/2.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.18/2.44  thf('19', plain,
% 2.18/2.44      (![X4 : $i, X6 : $i]:
% 2.18/2.44         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.18/2.44      inference('cnf', [status(esa)], [d3_tarski])).
% 2.18/2.44  thf(d1_xboole_0, axiom,
% 2.18/2.44    (![A:$i]:
% 2.18/2.44     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.18/2.44  thf('20', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.18/2.44      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.18/2.44  thf('21', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.18/2.44      inference('sup-', [status(thm)], ['19', '20'])).
% 2.18/2.44  thf('22', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.18/2.44      inference('sup-', [status(thm)], ['19', '20'])).
% 2.18/2.44  thf(d10_xboole_0, axiom,
% 2.18/2.44    (![A:$i,B:$i]:
% 2.18/2.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.18/2.44  thf('23', plain,
% 2.18/2.44      (![X7 : $i, X9 : $i]:
% 2.18/2.44         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.18/2.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.18/2.44  thf('24', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i]:
% 2.18/2.44         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.18/2.44      inference('sup-', [status(thm)], ['22', '23'])).
% 2.18/2.44  thf('25', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i]:
% 2.18/2.44         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.18/2.44      inference('sup-', [status(thm)], ['21', '24'])).
% 2.18/2.44  thf('26', plain,
% 2.18/2.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.18/2.44      inference('sup-', [status(thm)], ['18', '25'])).
% 2.18/2.44  thf('27', plain,
% 2.18/2.44      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.18/2.44      inference('sup-', [status(thm)], ['18', '25'])).
% 2.18/2.44  thf(t4_subset_1, axiom,
% 2.18/2.44    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.18/2.44  thf('28', plain,
% 2.18/2.44      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 2.18/2.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.18/2.44  thf(redefinition_r2_relset_1, axiom,
% 2.18/2.44    (![A:$i,B:$i,C:$i,D:$i]:
% 2.18/2.44     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.18/2.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.18/2.44       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.18/2.44  thf('29', plain,
% 2.18/2.44      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.18/2.44         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.18/2.44          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.18/2.44          | (r2_relset_1 @ X38 @ X39 @ X37 @ X40)
% 2.18/2.44          | ((X37) != (X40)))),
% 2.18/2.44      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.18/2.44  thf('30', plain,
% 2.18/2.44      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.18/2.44         ((r2_relset_1 @ X38 @ X39 @ X40 @ X40)
% 2.18/2.44          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.18/2.44      inference('simplify', [status(thm)], ['29'])).
% 2.18/2.44  thf('31', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.18/2.44      inference('sup-', [status(thm)], ['28', '30'])).
% 2.18/2.44  thf('32', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.18/2.44         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 2.18/2.44      inference('sup+', [status(thm)], ['27', '31'])).
% 2.18/2.44  thf('33', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.18/2.44         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 2.18/2.44          | ~ (v1_xboole_0 @ X0)
% 2.18/2.44          | ~ (v1_xboole_0 @ X1))),
% 2.18/2.44      inference('sup+', [status(thm)], ['26', '32'])).
% 2.18/2.44  thf('34', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('35', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 2.18/2.44      inference('sup-', [status(thm)], ['33', '34'])).
% 2.18/2.44  thf('36', plain,
% 2.18/2.44      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 2.18/2.44      inference('sup-', [status(thm)], ['17', '35'])).
% 2.18/2.44  thf('37', plain,
% 2.18/2.44      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.18/2.44      inference('sup+', [status(thm)], ['11', '12'])).
% 2.18/2.44  thf('38', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('39', plain,
% 2.18/2.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.18/2.44         (~ (v1_xboole_0 @ X31)
% 2.18/2.44          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 2.18/2.44          | (v1_xboole_0 @ X32))),
% 2.18/2.44      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.18/2.44  thf('40', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 2.18/2.44      inference('sup-', [status(thm)], ['38', '39'])).
% 2.18/2.44  thf('41', plain,
% 2.18/2.44      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 2.18/2.44      inference('sup-', [status(thm)], ['37', '40'])).
% 2.18/2.44  thf('42', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 2.18/2.44      inference('clc', [status(thm)], ['36', '41'])).
% 2.18/2.44  thf('43', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 2.18/2.44      inference('demod', [status(thm)], ['10', '42'])).
% 2.18/2.44  thf('44', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.18/2.44      inference('demod', [status(thm)], ['7', '43'])).
% 2.18/2.44  thf('45', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('46', plain,
% 2.18/2.44      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.18/2.44         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 2.18/2.44          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 2.18/2.44          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.18/2.44  thf('47', plain,
% 2.18/2.44      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.18/2.44        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 2.18/2.44      inference('sup-', [status(thm)], ['45', '46'])).
% 2.18/2.44  thf('48', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('49', plain,
% 2.18/2.44      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.18/2.44         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 2.18/2.44          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.18/2.44      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.18/2.44  thf('50', plain,
% 2.18/2.44      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 2.18/2.44      inference('sup-', [status(thm)], ['48', '49'])).
% 2.18/2.44  thf('51', plain,
% 2.18/2.44      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.18/2.44        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.18/2.44      inference('demod', [status(thm)], ['47', '50'])).
% 2.18/2.44  thf('52', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('53', plain,
% 2.18/2.44      (![X46 : $i, X47 : $i, X48 : $i]:
% 2.18/2.44         (~ (zip_tseitin_0 @ X46 @ X47)
% 2.18/2.44          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 2.18/2.44          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.18/2.44  thf('54', plain,
% 2.18/2.44      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.18/2.44        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.18/2.44      inference('sup-', [status(thm)], ['52', '53'])).
% 2.18/2.44  thf('55', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 2.18/2.44      inference('clc', [status(thm)], ['36', '41'])).
% 2.18/2.44  thf('56', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 2.18/2.44      inference('demod', [status(thm)], ['54', '55'])).
% 2.18/2.44  thf('57', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.18/2.44      inference('demod', [status(thm)], ['51', '56'])).
% 2.18/2.44  thf(t9_funct_1, axiom,
% 2.18/2.44    (![A:$i]:
% 2.18/2.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.18/2.44       ( ![B:$i]:
% 2.18/2.44         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.18/2.44           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.18/2.44               ( ![C:$i]:
% 2.18/2.44                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.18/2.44                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 2.18/2.44             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.18/2.44  thf('58', plain,
% 2.18/2.44      (![X26 : $i, X27 : $i]:
% 2.18/2.44         (~ (v1_relat_1 @ X26)
% 2.18/2.44          | ~ (v1_funct_1 @ X26)
% 2.18/2.44          | ((X27) = (X26))
% 2.18/2.44          | (r2_hidden @ (sk_C_1 @ X26 @ X27) @ (k1_relat_1 @ X27))
% 2.18/2.44          | ((k1_relat_1 @ X27) != (k1_relat_1 @ X26))
% 2.18/2.44          | ~ (v1_funct_1 @ X27)
% 2.18/2.44          | ~ (v1_relat_1 @ X27))),
% 2.18/2.44      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.18/2.44  thf('59', plain,
% 2.18/2.44      (![X0 : $i]:
% 2.18/2.44         (((sk_A) != (k1_relat_1 @ X0))
% 2.18/2.44          | ~ (v1_relat_1 @ sk_C_2)
% 2.18/2.44          | ~ (v1_funct_1 @ sk_C_2)
% 2.18/2.44          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 2.18/2.44          | ((sk_C_2) = (X0))
% 2.18/2.44          | ~ (v1_funct_1 @ X0)
% 2.18/2.44          | ~ (v1_relat_1 @ X0))),
% 2.18/2.44      inference('sup-', [status(thm)], ['57', '58'])).
% 2.18/2.44  thf('60', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf(cc2_relat_1, axiom,
% 2.18/2.44    (![A:$i]:
% 2.18/2.44     ( ( v1_relat_1 @ A ) =>
% 2.18/2.44       ( ![B:$i]:
% 2.18/2.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.18/2.44  thf('61', plain,
% 2.18/2.44      (![X17 : $i, X18 : $i]:
% 2.18/2.44         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 2.18/2.44          | (v1_relat_1 @ X17)
% 2.18/2.44          | ~ (v1_relat_1 @ X18))),
% 2.18/2.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.18/2.44  thf('62', plain,
% 2.18/2.44      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_2))),
% 2.18/2.44      inference('sup-', [status(thm)], ['60', '61'])).
% 2.18/2.44  thf(fc6_relat_1, axiom,
% 2.18/2.44    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.18/2.44  thf('63', plain,
% 2.18/2.44      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 2.18/2.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.18/2.44  thf('64', plain, ((v1_relat_1 @ sk_C_2)),
% 2.18/2.44      inference('demod', [status(thm)], ['62', '63'])).
% 2.18/2.44  thf('65', plain, ((v1_funct_1 @ sk_C_2)),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('66', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.18/2.44      inference('demod', [status(thm)], ['51', '56'])).
% 2.18/2.44  thf('67', plain,
% 2.18/2.44      (![X0 : $i]:
% 2.18/2.44         (((sk_A) != (k1_relat_1 @ X0))
% 2.18/2.44          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 2.18/2.44          | ((sk_C_2) = (X0))
% 2.18/2.44          | ~ (v1_funct_1 @ X0)
% 2.18/2.44          | ~ (v1_relat_1 @ X0))),
% 2.18/2.44      inference('demod', [status(thm)], ['59', '64', '65', '66'])).
% 2.18/2.44  thf('68', plain,
% 2.18/2.44      ((((sk_A) != (sk_A))
% 2.18/2.44        | ~ (v1_relat_1 @ sk_D)
% 2.18/2.44        | ~ (v1_funct_1 @ sk_D)
% 2.18/2.44        | ((sk_C_2) = (sk_D))
% 2.18/2.44        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.18/2.44      inference('sup-', [status(thm)], ['44', '67'])).
% 2.18/2.44  thf('69', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('70', plain,
% 2.18/2.44      (![X17 : $i, X18 : $i]:
% 2.18/2.44         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 2.18/2.44          | (v1_relat_1 @ X17)
% 2.18/2.44          | ~ (v1_relat_1 @ X18))),
% 2.18/2.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.18/2.44  thf('71', plain,
% 2.18/2.44      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 2.18/2.44      inference('sup-', [status(thm)], ['69', '70'])).
% 2.18/2.44  thf('72', plain,
% 2.18/2.44      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 2.18/2.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.18/2.44  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 2.18/2.44      inference('demod', [status(thm)], ['71', '72'])).
% 2.18/2.44  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('75', plain,
% 2.18/2.44      ((((sk_A) != (sk_A))
% 2.18/2.44        | ((sk_C_2) = (sk_D))
% 2.18/2.44        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.18/2.44      inference('demod', [status(thm)], ['68', '73', '74'])).
% 2.18/2.44  thf('76', plain,
% 2.18/2.44      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 2.18/2.44      inference('simplify', [status(thm)], ['75'])).
% 2.18/2.44  thf('77', plain,
% 2.18/2.44      (![X49 : $i]:
% 2.18/2.44         (((k1_funct_1 @ sk_C_2 @ X49) = (k1_funct_1 @ sk_D @ X49))
% 2.18/2.44          | ~ (r2_hidden @ X49 @ sk_A))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('78', plain,
% 2.18/2.44      ((((sk_C_2) = (sk_D))
% 2.18/2.44        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.18/2.44            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 2.18/2.44      inference('sup-', [status(thm)], ['76', '77'])).
% 2.18/2.44  thf('79', plain,
% 2.18/2.44      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.18/2.44         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 2.18/2.44      inference('condensation', [status(thm)], ['78'])).
% 2.18/2.44  thf('80', plain,
% 2.18/2.44      (![X26 : $i, X27 : $i]:
% 2.18/2.44         (~ (v1_relat_1 @ X26)
% 2.18/2.44          | ~ (v1_funct_1 @ X26)
% 2.18/2.44          | ((X27) = (X26))
% 2.18/2.44          | ((k1_funct_1 @ X27 @ (sk_C_1 @ X26 @ X27))
% 2.18/2.44              != (k1_funct_1 @ X26 @ (sk_C_1 @ X26 @ X27)))
% 2.18/2.44          | ((k1_relat_1 @ X27) != (k1_relat_1 @ X26))
% 2.18/2.44          | ~ (v1_funct_1 @ X27)
% 2.18/2.44          | ~ (v1_relat_1 @ X27))),
% 2.18/2.44      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.18/2.44  thf('81', plain,
% 2.18/2.44      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.18/2.44          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.18/2.44        | ~ (v1_relat_1 @ sk_C_2)
% 2.18/2.44        | ~ (v1_funct_1 @ sk_C_2)
% 2.18/2.44        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 2.18/2.44        | ((sk_C_2) = (sk_D))
% 2.18/2.44        | ~ (v1_funct_1 @ sk_D)
% 2.18/2.44        | ~ (v1_relat_1 @ sk_D))),
% 2.18/2.44      inference('sup-', [status(thm)], ['79', '80'])).
% 2.18/2.44  thf('82', plain, ((v1_relat_1 @ sk_C_2)),
% 2.18/2.44      inference('demod', [status(thm)], ['62', '63'])).
% 2.18/2.44  thf('83', plain, ((v1_funct_1 @ sk_C_2)),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.18/2.44      inference('demod', [status(thm)], ['51', '56'])).
% 2.18/2.44  thf('85', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.18/2.44      inference('demod', [status(thm)], ['7', '43'])).
% 2.18/2.44  thf('86', plain, ((v1_funct_1 @ sk_D)),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 2.18/2.44      inference('demod', [status(thm)], ['71', '72'])).
% 2.18/2.44  thf('88', plain,
% 2.18/2.44      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.18/2.44          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.18/2.44        | ((sk_A) != (sk_A))
% 2.18/2.44        | ((sk_C_2) = (sk_D)))),
% 2.18/2.44      inference('demod', [status(thm)],
% 2.18/2.44                ['81', '82', '83', '84', '85', '86', '87'])).
% 2.18/2.44  thf('89', plain, (((sk_C_2) = (sk_D))),
% 2.18/2.44      inference('simplify', [status(thm)], ['88'])).
% 2.18/2.44  thf('90', plain,
% 2.18/2.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.18/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.18/2.44  thf('91', plain,
% 2.18/2.44      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.18/2.44         ((r2_relset_1 @ X38 @ X39 @ X40 @ X40)
% 2.18/2.44          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.18/2.44      inference('simplify', [status(thm)], ['29'])).
% 2.18/2.44  thf('92', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 2.18/2.44      inference('sup-', [status(thm)], ['90', '91'])).
% 2.18/2.44  thf('93', plain, ($false),
% 2.18/2.44      inference('demod', [status(thm)], ['0', '89', '92'])).
% 2.18/2.44  
% 2.18/2.44  % SZS output end Refutation
% 2.18/2.44  
% 2.18/2.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
