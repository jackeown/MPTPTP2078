%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nLdWalouom

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:59 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 231 expanded)
%              Number of leaves         :   47 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  871 (2832 expanded)
%              Number of equality atoms :   57 ( 150 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X51 )
      | ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ X51 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k7_relset_1 @ X39 @ X40 @ X38 @ X41 )
        = ( k9_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('13',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('15',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ( X44
        = ( k1_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( zip_tseitin_1 @ X46 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('19',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( zip_tseitin_0 @ X47 @ X48 )
      | ( zip_tseitin_1 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
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

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('32',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['29','33'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( ( k11_relat_1 @ X27 @ X26 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( v4_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k9_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k11_relat_1 @ X18 @ X19 )
        = ( k9_relat_1 @ X18 @ ( k1_tarski @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('55',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('56',plain,
    ( ( k11_relat_1 @ sk_D_1 @ sk_A )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','39','40','56'])).

thf('58',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['28','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('61',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k7_relset_1 @ X39 @ X40 @ X38 @ X41 )
        = ( k9_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('67',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['65','66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nLdWalouom
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.37/1.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.57  % Solved by: fo/fo7.sh
% 1.37/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.57  % done 584 iterations in 1.119s
% 1.37/1.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.57  % SZS output start Refutation
% 1.37/1.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.37/1.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.37/1.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.37/1.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.37/1.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.37/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.37/1.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.37/1.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.37/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.37/1.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.37/1.57  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.37/1.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.37/1.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.37/1.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.37/1.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.37/1.57  thf(sk_C_type, type, sk_C: $i).
% 1.37/1.57  thf(d10_xboole_0, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.37/1.57  thf('0', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.37/1.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.37/1.57  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.37/1.57      inference('simplify', [status(thm)], ['0'])).
% 1.37/1.57  thf(t4_funct_2, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.37/1.57       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.37/1.57         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.37/1.57           ( m1_subset_1 @
% 1.37/1.57             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.37/1.57  thf('2', plain,
% 1.37/1.57      (![X50 : $i, X51 : $i]:
% 1.37/1.57         (~ (r1_tarski @ (k2_relat_1 @ X50) @ X51)
% 1.37/1.57          | (m1_subset_1 @ X50 @ 
% 1.37/1.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ X51)))
% 1.37/1.57          | ~ (v1_funct_1 @ X50)
% 1.37/1.57          | ~ (v1_relat_1 @ X50))),
% 1.37/1.57      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.37/1.57  thf('3', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X0)
% 1.37/1.57          | ~ (v1_funct_1 @ X0)
% 1.37/1.57          | (m1_subset_1 @ X0 @ 
% 1.37/1.57             (k1_zfmisc_1 @ 
% 1.37/1.57              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['1', '2'])).
% 1.37/1.57  thf(redefinition_k7_relset_1, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.37/1.57  thf('4', plain,
% 1.37/1.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.37/1.57         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.37/1.57          | ((k7_relset_1 @ X39 @ X40 @ X38 @ X41) = (k9_relat_1 @ X38 @ X41)))),
% 1.37/1.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.37/1.57  thf('5', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i]:
% 1.37/1.57         (~ (v1_funct_1 @ X0)
% 1.37/1.57          | ~ (v1_relat_1 @ X0)
% 1.37/1.57          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 1.37/1.57              = (k9_relat_1 @ X0 @ X1)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.37/1.57  thf('6', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X0)
% 1.37/1.57          | ~ (v1_funct_1 @ X0)
% 1.37/1.57          | (m1_subset_1 @ X0 @ 
% 1.37/1.57             (k1_zfmisc_1 @ 
% 1.37/1.57              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['1', '2'])).
% 1.37/1.57  thf(dt_k7_relset_1, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.57       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.37/1.57  thf('7', plain,
% 1.37/1.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.37/1.57         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.37/1.57          | (m1_subset_1 @ (k7_relset_1 @ X32 @ X33 @ X31 @ X34) @ 
% 1.37/1.57             (k1_zfmisc_1 @ X33)))),
% 1.37/1.57      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.37/1.57  thf('8', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i]:
% 1.37/1.57         (~ (v1_funct_1 @ X0)
% 1.37/1.57          | ~ (v1_relat_1 @ X0)
% 1.37/1.57          | (m1_subset_1 @ 
% 1.37/1.57             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 1.37/1.57             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['6', '7'])).
% 1.37/1.57  thf(t3_subset, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.37/1.57  thf('9', plain,
% 1.37/1.57      (![X15 : $i, X16 : $i]:
% 1.37/1.57         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.37/1.57      inference('cnf', [status(esa)], [t3_subset])).
% 1.37/1.57  thf('10', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X0)
% 1.37/1.57          | ~ (v1_funct_1 @ X0)
% 1.37/1.57          | (r1_tarski @ 
% 1.37/1.57             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 1.37/1.57             (k2_relat_1 @ X0)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['8', '9'])).
% 1.37/1.57  thf('11', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i]:
% 1.37/1.57         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 1.37/1.57          | ~ (v1_relat_1 @ X1)
% 1.37/1.57          | ~ (v1_funct_1 @ X1)
% 1.37/1.57          | ~ (v1_funct_1 @ X1)
% 1.37/1.57          | ~ (v1_relat_1 @ X1))),
% 1.37/1.57      inference('sup+', [status(thm)], ['5', '10'])).
% 1.37/1.57  thf('12', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i]:
% 1.37/1.57         (~ (v1_funct_1 @ X1)
% 1.37/1.57          | ~ (v1_relat_1 @ X1)
% 1.37/1.57          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 1.37/1.57      inference('simplify', [status(thm)], ['11'])).
% 1.37/1.57  thf(t64_funct_2, conjecture,
% 1.37/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.37/1.57         ( m1_subset_1 @
% 1.37/1.57           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.37/1.57       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.37/1.57         ( r1_tarski @
% 1.37/1.57           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.37/1.57           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 1.37/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.37/1.57            ( m1_subset_1 @
% 1.37/1.57              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.37/1.57          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.37/1.57            ( r1_tarski @
% 1.37/1.57              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.37/1.57              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 1.37/1.57    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 1.37/1.57  thf('13', plain,
% 1.37/1.57      (~ (r1_tarski @ 
% 1.37/1.57          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 1.37/1.57          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('14', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf(d1_funct_2, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i]:
% 1.37/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.37/1.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.37/1.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.37/1.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.37/1.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.37/1.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.37/1.57  thf(zf_stmt_1, axiom,
% 1.37/1.57    (![C:$i,B:$i,A:$i]:
% 1.37/1.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.37/1.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.37/1.57  thf('15', plain,
% 1.37/1.57      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.37/1.57         (~ (v1_funct_2 @ X46 @ X44 @ X45)
% 1.37/1.57          | ((X44) = (k1_relset_1 @ X44 @ X45 @ X46))
% 1.37/1.57          | ~ (zip_tseitin_1 @ X46 @ X45 @ X44))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.37/1.57  thf('16', plain,
% 1.37/1.57      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 1.37/1.57        | ((k1_tarski @ sk_A)
% 1.37/1.57            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['14', '15'])).
% 1.37/1.57  thf(zf_stmt_2, axiom,
% 1.37/1.57    (![B:$i,A:$i]:
% 1.37/1.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.37/1.57       ( zip_tseitin_0 @ B @ A ) ))).
% 1.37/1.57  thf('17', plain,
% 1.37/1.57      (![X42 : $i, X43 : $i]:
% 1.37/1.57         ((zip_tseitin_0 @ X42 @ X43) | ((X42) = (k1_xboole_0)))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.37/1.57  thf('18', plain,
% 1.37/1.57      ((m1_subset_1 @ sk_D_1 @ 
% 1.37/1.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.37/1.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.37/1.57  thf(zf_stmt_5, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i]:
% 1.37/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.37/1.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.37/1.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.37/1.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.37/1.57  thf('19', plain,
% 1.37/1.57      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.37/1.57         (~ (zip_tseitin_0 @ X47 @ X48)
% 1.37/1.57          | (zip_tseitin_1 @ X49 @ X47 @ X48)
% 1.37/1.57          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47))))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.37/1.57  thf('20', plain,
% 1.37/1.57      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 1.37/1.57        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['18', '19'])).
% 1.37/1.57  thf('21', plain,
% 1.37/1.57      ((((sk_B) = (k1_xboole_0))
% 1.37/1.57        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['17', '20'])).
% 1.37/1.57  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('23', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 1.37/1.57      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 1.37/1.57  thf('24', plain,
% 1.37/1.57      ((m1_subset_1 @ sk_D_1 @ 
% 1.37/1.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf(redefinition_k1_relset_1, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i]:
% 1.37/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.37/1.57  thf('25', plain,
% 1.37/1.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.37/1.57         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 1.37/1.57          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.37/1.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.37/1.57  thf('26', plain,
% 1.37/1.57      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 1.37/1.57         = (k1_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('sup-', [status(thm)], ['24', '25'])).
% 1.37/1.57  thf('27', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('demod', [status(thm)], ['16', '23', '26'])).
% 1.37/1.57  thf('28', plain,
% 1.37/1.57      (~ (r1_tarski @ 
% 1.37/1.57          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 1.37/1.57          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.37/1.57      inference('demod', [status(thm)], ['13', '27'])).
% 1.37/1.57  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('demod', [status(thm)], ['16', '23', '26'])).
% 1.37/1.57  thf(t69_enumset1, axiom,
% 1.37/1.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.37/1.57  thf('30', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.37/1.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.37/1.57  thf(d2_tarski, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i]:
% 1.37/1.57     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.37/1.57       ( ![D:$i]:
% 1.37/1.57         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.37/1.57  thf('31', plain,
% 1.37/1.57      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.37/1.57         (((X4) != (X3))
% 1.37/1.57          | (r2_hidden @ X4 @ X5)
% 1.37/1.57          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 1.37/1.57      inference('cnf', [status(esa)], [d2_tarski])).
% 1.37/1.57  thf('32', plain,
% 1.37/1.57      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 1.37/1.57      inference('simplify', [status(thm)], ['31'])).
% 1.37/1.57  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.37/1.57      inference('sup+', [status(thm)], ['30', '32'])).
% 1.37/1.57  thf('34', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('sup+', [status(thm)], ['29', '33'])).
% 1.37/1.57  thf(t117_funct_1, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.37/1.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.37/1.57         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.37/1.57  thf('35', plain,
% 1.37/1.57      (![X26 : $i, X27 : $i]:
% 1.37/1.57         (~ (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 1.37/1.57          | ((k11_relat_1 @ X27 @ X26) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 1.37/1.57          | ~ (v1_funct_1 @ X27)
% 1.37/1.57          | ~ (v1_relat_1 @ X27))),
% 1.37/1.57      inference('cnf', [status(esa)], [t117_funct_1])).
% 1.37/1.57  thf('36', plain,
% 1.37/1.57      ((~ (v1_relat_1 @ sk_D_1)
% 1.37/1.57        | ~ (v1_funct_1 @ sk_D_1)
% 1.37/1.57        | ((k11_relat_1 @ sk_D_1 @ sk_A)
% 1.37/1.57            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['34', '35'])).
% 1.37/1.57  thf('37', plain,
% 1.37/1.57      ((m1_subset_1 @ sk_D_1 @ 
% 1.37/1.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf(cc1_relset_1, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i]:
% 1.37/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.57       ( v1_relat_1 @ C ) ))).
% 1.37/1.57  thf('38', plain,
% 1.37/1.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.37/1.57         ((v1_relat_1 @ X28)
% 1.37/1.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.37/1.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.37/1.57  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 1.37/1.57      inference('sup-', [status(thm)], ['37', '38'])).
% 1.37/1.57  thf('40', plain, ((v1_funct_1 @ sk_D_1)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.37/1.57      inference('simplify', [status(thm)], ['0'])).
% 1.37/1.57  thf(d18_relat_1, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( v1_relat_1 @ B ) =>
% 1.37/1.57       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.37/1.57  thf('42', plain,
% 1.37/1.57      (![X20 : $i, X21 : $i]:
% 1.37/1.57         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 1.37/1.57          | (v4_relat_1 @ X20 @ X21)
% 1.37/1.57          | ~ (v1_relat_1 @ X20))),
% 1.37/1.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.37/1.57  thf('43', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['41', '42'])).
% 1.37/1.57  thf(t209_relat_1, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.37/1.57       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.37/1.57  thf('44', plain,
% 1.37/1.57      (![X24 : $i, X25 : $i]:
% 1.37/1.57         (((X24) = (k7_relat_1 @ X24 @ X25))
% 1.37/1.57          | ~ (v4_relat_1 @ X24 @ X25)
% 1.37/1.57          | ~ (v1_relat_1 @ X24))),
% 1.37/1.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.37/1.57  thf('45', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X0)
% 1.37/1.57          | ~ (v1_relat_1 @ X0)
% 1.37/1.57          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['43', '44'])).
% 1.37/1.57  thf('46', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 1.37/1.57      inference('simplify', [status(thm)], ['45'])).
% 1.37/1.57  thf(t148_relat_1, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( v1_relat_1 @ B ) =>
% 1.37/1.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.37/1.57  thf('47', plain,
% 1.37/1.57      (![X22 : $i, X23 : $i]:
% 1.37/1.57         (((k2_relat_1 @ (k7_relat_1 @ X22 @ X23)) = (k9_relat_1 @ X22 @ X23))
% 1.37/1.57          | ~ (v1_relat_1 @ X22))),
% 1.37/1.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.37/1.57  thf('48', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 1.37/1.57          | ~ (v1_relat_1 @ X0)
% 1.37/1.57          | ~ (v1_relat_1 @ X0))),
% 1.37/1.57      inference('sup+', [status(thm)], ['46', '47'])).
% 1.37/1.57  thf('49', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X0)
% 1.37/1.57          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 1.37/1.57      inference('simplify', [status(thm)], ['48'])).
% 1.37/1.57  thf('50', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('demod', [status(thm)], ['16', '23', '26'])).
% 1.37/1.57  thf(d16_relat_1, axiom,
% 1.37/1.57    (![A:$i]:
% 1.37/1.57     ( ( v1_relat_1 @ A ) =>
% 1.37/1.57       ( ![B:$i]:
% 1.37/1.57         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 1.37/1.57  thf('51', plain,
% 1.37/1.57      (![X18 : $i, X19 : $i]:
% 1.37/1.57         (((k11_relat_1 @ X18 @ X19) = (k9_relat_1 @ X18 @ (k1_tarski @ X19)))
% 1.37/1.57          | ~ (v1_relat_1 @ X18))),
% 1.37/1.57      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.37/1.57  thf('52', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         (((k11_relat_1 @ X0 @ sk_A)
% 1.37/1.57            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D_1)))
% 1.37/1.57          | ~ (v1_relat_1 @ X0))),
% 1.37/1.57      inference('sup+', [status(thm)], ['50', '51'])).
% 1.37/1.57  thf('53', plain,
% 1.37/1.57      ((((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))
% 1.37/1.57        | ~ (v1_relat_1 @ sk_D_1)
% 1.37/1.57        | ~ (v1_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('sup+', [status(thm)], ['49', '52'])).
% 1.37/1.57  thf('54', plain, ((v1_relat_1 @ sk_D_1)),
% 1.37/1.57      inference('sup-', [status(thm)], ['37', '38'])).
% 1.37/1.57  thf('55', plain, ((v1_relat_1 @ sk_D_1)),
% 1.37/1.57      inference('sup-', [status(thm)], ['37', '38'])).
% 1.37/1.57  thf('56', plain, (((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.37/1.57  thf('57', plain,
% 1.37/1.57      (((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 1.37/1.57      inference('demod', [status(thm)], ['36', '39', '40', '56'])).
% 1.37/1.57  thf('58', plain,
% 1.37/1.57      (~ (r1_tarski @ 
% 1.37/1.57          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 1.37/1.57          (k2_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('demod', [status(thm)], ['28', '57'])).
% 1.37/1.57  thf('59', plain,
% 1.37/1.57      ((m1_subset_1 @ sk_D_1 @ 
% 1.37/1.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('60', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('demod', [status(thm)], ['16', '23', '26'])).
% 1.37/1.57  thf('61', plain,
% 1.37/1.57      ((m1_subset_1 @ sk_D_1 @ 
% 1.37/1.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 1.37/1.57      inference('demod', [status(thm)], ['59', '60'])).
% 1.37/1.57  thf('62', plain,
% 1.37/1.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.37/1.57         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.37/1.57          | ((k7_relset_1 @ X39 @ X40 @ X38 @ X41) = (k9_relat_1 @ X38 @ X41)))),
% 1.37/1.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.37/1.57  thf('63', plain,
% 1.37/1.57      (![X0 : $i]:
% 1.37/1.57         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ X0)
% 1.37/1.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 1.37/1.57      inference('sup-', [status(thm)], ['61', '62'])).
% 1.37/1.57  thf('64', plain,
% 1.37/1.57      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))),
% 1.37/1.57      inference('demod', [status(thm)], ['58', '63'])).
% 1.37/1.57  thf('65', plain, ((~ (v1_relat_1 @ sk_D_1) | ~ (v1_funct_1 @ sk_D_1))),
% 1.37/1.57      inference('sup-', [status(thm)], ['12', '64'])).
% 1.37/1.57  thf('66', plain, ((v1_relat_1 @ sk_D_1)),
% 1.37/1.57      inference('sup-', [status(thm)], ['37', '38'])).
% 1.37/1.57  thf('67', plain, ((v1_funct_1 @ sk_D_1)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('68', plain, ($false),
% 1.37/1.57      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.37/1.57  
% 1.37/1.57  % SZS output end Refutation
% 1.37/1.57  
% 1.37/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
