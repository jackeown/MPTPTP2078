%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x4xqnMeZ0s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:21 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 139 expanded)
%              Number of leaves         :   41 (  57 expanded)
%              Depth                    :   19
%              Number of atoms          :  751 (1354 expanded)
%              Number of equality atoms :   67 ( 112 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    v1_funct_2 @ sk_D_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X16 ) @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('12',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['3','20','23'])).

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

thf('25',plain,(
    ! [X23: $i,X25: $i,X27: $i,X28: $i] :
      ( ( X25
       != ( k2_relat_1 @ X23 ) )
      | ( r2_hidden @ X27 @ X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X23 ) )
      | ( X27
       != ( k1_funct_1 @ X23 @ X28 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('26',plain,(
    ! [X23: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X23 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X23 @ X28 ) @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['27','28','31'])).

thf('33',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X32 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('36',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('46',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('48',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('54',plain,(
    ! [X3: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( X7 = X6 )
      | ( X7 = X3 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('55',plain,(
    ! [X3: $i,X6: $i,X7: $i] :
      ( ( X7 = X3 )
      | ( X7 = X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x4xqnMeZ0s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 251 iterations in 0.212s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.67  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.67  thf(t65_funct_2, conjecture,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.47/0.67         ( m1_subset_1 @
% 0.47/0.67           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.67       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.47/0.67            ( m1_subset_1 @
% 0.47/0.67              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.47/0.67          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.47/0.67  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('1', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(d1_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_1, axiom,
% 0.47/0.67    (![C:$i,B:$i,A:$i]:
% 0.47/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.47/0.67         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.47/0.67          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.47/0.67          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.47/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.67  thf(zf_stmt_2, axiom,
% 0.47/0.67    (![B:$i,A:$i]:
% 0.47/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X41 : $i, X42 : $i]:
% 0.47/0.67         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf(t113_zfmisc_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (![X13 : $i, X14 : $i]:
% 0.47/0.67         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.47/0.67          | ((X13) != (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.47/0.67      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.47/0.67      inference('sup+', [status(thm)], ['4', '6'])).
% 0.47/0.67  thf(t130_zfmisc_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.47/0.67       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.67         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      (![X15 : $i, X16 : $i]:
% 0.47/0.67         (((X15) = (k1_xboole_0))
% 0.47/0.67          | ((k2_zfmisc_1 @ (k1_tarski @ X16) @ X15) != (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.67          | (zip_tseitin_0 @ (k1_tarski @ X1) @ X2)
% 0.47/0.67          | ((X0) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (((X0) = (k1_xboole_0)) | (zip_tseitin_0 @ (k1_tarski @ X1) @ X2))),
% 0.47/0.67      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D_3 @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_5, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.47/0.67         (~ (zip_tseitin_0 @ X46 @ X47)
% 0.47/0.67          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 0.47/0.67          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      (((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.47/0.67        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((X0) = (k1_xboole_0))
% 0.47/0.67          | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['10', '13'])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((X0) = (k1_xboole_0))
% 0.47/0.67          | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['10', '13'])).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((X1) = (X0))
% 0.47/0.67          | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.47/0.67          | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.47/0.67      inference('sup+', [status(thm)], ['14', '15'])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.47/0.67          | ((X1) = (X0)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.67  thf('18', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) != (sk_B_1))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((X0) != (sk_B_1))
% 0.47/0.67          | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('20', plain, ((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.47/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D_3 @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.47/0.67          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)
% 0.47/0.67         = (k1_relat_1 @ sk_D_3))),
% 0.47/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.67  thf('24', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.47/0.67      inference('demod', [status(thm)], ['3', '20', '23'])).
% 0.47/0.67  thf(d5_funct_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.47/0.67           ( ![C:$i]:
% 0.47/0.67             ( ( r2_hidden @ C @ B ) <=>
% 0.47/0.67               ( ?[D:$i]:
% 0.47/0.67                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.47/0.67                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      (![X23 : $i, X25 : $i, X27 : $i, X28 : $i]:
% 0.47/0.67         (((X25) != (k2_relat_1 @ X23))
% 0.47/0.67          | (r2_hidden @ X27 @ X25)
% 0.47/0.67          | ~ (r2_hidden @ X28 @ (k1_relat_1 @ X23))
% 0.47/0.67          | ((X27) != (k1_funct_1 @ X23 @ X28))
% 0.47/0.67          | ~ (v1_funct_1 @ X23)
% 0.47/0.67          | ~ (v1_relat_1 @ X23))),
% 0.47/0.67      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      (![X23 : $i, X28 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X23)
% 0.47/0.67          | ~ (v1_funct_1 @ X23)
% 0.47/0.67          | ~ (r2_hidden @ X28 @ (k1_relat_1 @ X23))
% 0.47/0.67          | (r2_hidden @ (k1_funct_1 @ X23 @ X28) @ (k2_relat_1 @ X23)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['25'])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.47/0.67          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3))
% 0.47/0.67          | ~ (v1_funct_1 @ sk_D_3)
% 0.47/0.67          | ~ (v1_relat_1 @ sk_D_3))),
% 0.47/0.67      inference('sup-', [status(thm)], ['24', '26'])).
% 0.47/0.67  thf('28', plain, ((v1_funct_1 @ sk_D_3)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D_3 @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( v1_relat_1 @ C ) ))).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.47/0.67         ((v1_relat_1 @ X29)
% 0.47/0.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.67  thf('31', plain, ((v1_relat_1 @ sk_D_3)),
% 0.47/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.47/0.67          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3)))),
% 0.47/0.67      inference('demod', [status(thm)], ['27', '28', '31'])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k2_relat_1 @ sk_D_3))),
% 0.47/0.67      inference('sup-', [status(thm)], ['0', '32'])).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D_3 @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(dt_k2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.67  thf('35', plain,
% 0.47/0.67      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.67         ((m1_subset_1 @ (k2_relset_1 @ X32 @ X33 @ X34) @ (k1_zfmisc_1 @ X33))
% 0.47/0.67          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3) @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D_3 @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.47/0.67         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.47/0.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)
% 0.47/0.67         = (k2_relat_1 @ sk_D_3))),
% 0.47/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      ((m1_subset_1 @ (k2_relat_1 @ sk_D_3) @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.47/0.67      inference('demod', [status(thm)], ['36', '39'])).
% 0.47/0.67  thf(t4_subset, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.47/0.67       ( m1_subset_1 @ A @ C ) ))).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X19 @ X20)
% 0.47/0.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.47/0.67          | (m1_subset_1 @ X19 @ X21))),
% 0.47/0.67      inference('cnf', [status(esa)], [t4_subset])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.47/0.67          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      ((m1_subset_1 @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['33', '42'])).
% 0.47/0.67  thf(t2_subset, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ A @ B ) =>
% 0.47/0.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      (![X17 : $i, X18 : $i]:
% 0.47/0.67         ((r2_hidden @ X17 @ X18)
% 0.47/0.67          | (v1_xboole_0 @ X18)
% 0.47/0.67          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.47/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.47/0.67        | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.67  thf(t69_enumset1, axiom,
% 0.47/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.67  thf('46', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.67  thf(d2_tarski, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.47/0.67       ( ![D:$i]:
% 0.47/0.67         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.47/0.67  thf('47', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.67         (((X4) != (X3))
% 0.47/0.67          | (r2_hidden @ X4 @ X5)
% 0.47/0.67          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d2_tarski])).
% 0.47/0.67  thf('48', plain,
% 0.47/0.67      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 0.47/0.67      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.67  thf(d1_xboole_0, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.67  thf('51', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['46', '50'])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.47/0.67      inference('clc', [status(thm)], ['45', '51'])).
% 0.47/0.67  thf('53', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.67  thf('54', plain,
% 0.47/0.67      (![X3 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X7 @ X5)
% 0.47/0.67          | ((X7) = (X6))
% 0.47/0.67          | ((X7) = (X3))
% 0.47/0.67          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d2_tarski])).
% 0.47/0.67  thf('55', plain,
% 0.47/0.67      (![X3 : $i, X6 : $i, X7 : $i]:
% 0.47/0.67         (((X7) = (X3))
% 0.47/0.67          | ((X7) = (X6))
% 0.47/0.67          | ~ (r2_hidden @ X7 @ (k2_tarski @ X6 @ X3)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['54'])).
% 0.47/0.67  thf('56', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['53', '55'])).
% 0.47/0.67  thf('57', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['56'])).
% 0.47/0.67  thf('58', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) = (sk_B_1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['52', '57'])).
% 0.47/0.67  thf('59', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) != (sk_B_1))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('60', plain, ($false),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
