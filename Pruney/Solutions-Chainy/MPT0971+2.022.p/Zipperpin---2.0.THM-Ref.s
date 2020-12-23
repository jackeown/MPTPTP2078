%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.36QSXNHPkT

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:30 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 162 expanded)
%              Number of leaves         :   44 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  710 (1667 expanded)
%              Number of equality atoms :   48 (  86 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( X30
       != ( k2_relat_1 @ X28 ) )
      | ( r2_hidden @ ( sk_D_2 @ X31 @ X28 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X28: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r2_hidden @ X31 @ ( k2_relat_1 @ X28 ) )
      | ( r2_hidden @ ( sk_D_2 @ X31 @ X28 ) @ ( k1_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B ),
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

thf('16',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('24',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v5_relat_1 @ sk_D_3 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v5_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['11','12'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_1 @ ( k2_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_1 @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['35','41'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X16 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['26','50'])).

thf('52',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['21','51'])).

thf('53',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_D_3 ) @ sk_A ),
    inference(demod,[status(thm)],['14','52'])).

thf('54',plain,(
    ! [X51: $i] :
      ( ~ ( r2_hidden @ X51 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_3 @ X51 )
       != sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ sk_D_3 ) )
 != sk_C_1 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('57',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( X30
       != ( k2_relat_1 @ X28 ) )
      | ( X31
        = ( k1_funct_1 @ X28 @ ( sk_D_2 @ X31 @ X28 ) ) )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('58',plain,(
    ! [X28: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r2_hidden @ X31 @ ( k2_relat_1 @ X28 ) )
      | ( X31
        = ( k1_funct_1 @ X28 @ ( sk_D_2 @ X31 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ sk_D_3 ) ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['11','12'])).

thf('62',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.36QSXNHPkT
% 0.15/0.37  % Computer   : n023.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 18:02:06 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.57/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.75  % Solved by: fo/fo7.sh
% 0.57/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.75  % done 307 iterations in 0.268s
% 0.57/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.75  % SZS output start Refutation
% 0.57/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.57/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.57/0.75  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.57/0.75  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.57/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.57/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.57/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.75  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.57/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.57/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.57/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.57/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.57/0.75  thf(t17_funct_2, conjecture,
% 0.57/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.57/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.57/0.75       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.57/0.75            ( ![E:$i]:
% 0.57/0.75              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.57/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.75        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.57/0.75            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.57/0.75          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.57/0.75               ( ![E:$i]:
% 0.57/0.75                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.57/0.75                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.57/0.75    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.57/0.75  thf('0', plain,
% 0.57/0.75      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_3))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('1', plain,
% 0.57/0.75      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(redefinition_k2_relset_1, axiom,
% 0.57/0.75    (![A:$i,B:$i,C:$i]:
% 0.57/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.57/0.75  thf('2', plain,
% 0.57/0.75      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.57/0.75         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 0.57/0.75          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.57/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.57/0.75  thf('3', plain,
% 0.57/0.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.75  thf('4', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('demod', [status(thm)], ['0', '3'])).
% 0.57/0.75  thf(d5_funct_1, axiom,
% 0.57/0.75    (![A:$i]:
% 0.57/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.57/0.75       ( ![B:$i]:
% 0.57/0.75         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.57/0.75           ( ![C:$i]:
% 0.57/0.75             ( ( r2_hidden @ C @ B ) <=>
% 0.57/0.75               ( ?[D:$i]:
% 0.57/0.75                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.57/0.75                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.57/0.75  thf('5', plain,
% 0.57/0.75      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.57/0.75         (((X30) != (k2_relat_1 @ X28))
% 0.57/0.75          | (r2_hidden @ (sk_D_2 @ X31 @ X28) @ (k1_relat_1 @ X28))
% 0.57/0.75          | ~ (r2_hidden @ X31 @ X30)
% 0.57/0.75          | ~ (v1_funct_1 @ X28)
% 0.57/0.75          | ~ (v1_relat_1 @ X28))),
% 0.57/0.75      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.57/0.75  thf('6', plain,
% 0.57/0.75      (![X28 : $i, X31 : $i]:
% 0.57/0.75         (~ (v1_relat_1 @ X28)
% 0.57/0.75          | ~ (v1_funct_1 @ X28)
% 0.57/0.75          | ~ (r2_hidden @ X31 @ (k2_relat_1 @ X28))
% 0.57/0.75          | (r2_hidden @ (sk_D_2 @ X31 @ X28) @ (k1_relat_1 @ X28)))),
% 0.57/0.75      inference('simplify', [status(thm)], ['5'])).
% 0.57/0.75  thf('7', plain,
% 0.57/0.75      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_D_3) @ (k1_relat_1 @ sk_D_3))
% 0.57/0.75        | ~ (v1_funct_1 @ sk_D_3)
% 0.57/0.75        | ~ (v1_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('sup-', [status(thm)], ['4', '6'])).
% 0.57/0.75  thf('8', plain, ((v1_funct_1 @ sk_D_3)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('9', plain,
% 0.57/0.75      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(cc2_relat_1, axiom,
% 0.57/0.75    (![A:$i]:
% 0.57/0.75     ( ( v1_relat_1 @ A ) =>
% 0.57/0.75       ( ![B:$i]:
% 0.57/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.57/0.75  thf('10', plain,
% 0.57/0.75      (![X21 : $i, X22 : $i]:
% 0.57/0.75         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.57/0.75          | (v1_relat_1 @ X21)
% 0.57/0.75          | ~ (v1_relat_1 @ X22))),
% 0.57/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.57/0.75  thf('11', plain,
% 0.57/0.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('sup-', [status(thm)], ['9', '10'])).
% 0.57/0.75  thf(fc6_relat_1, axiom,
% 0.57/0.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.57/0.75  thf('12', plain,
% 0.57/0.75      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 0.57/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.57/0.75  thf('13', plain, ((v1_relat_1 @ sk_D_3)),
% 0.57/0.75      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.75  thf('14', plain,
% 0.57/0.75      ((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.57/0.75  thf('15', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(d1_funct_2, axiom,
% 0.57/0.75    (![A:$i,B:$i,C:$i]:
% 0.57/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.57/0.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.57/0.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.57/0.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.57/0.75  thf(zf_stmt_1, axiom,
% 0.57/0.75    (![C:$i,B:$i,A:$i]:
% 0.57/0.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.57/0.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.57/0.75  thf('16', plain,
% 0.57/0.75      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.57/0.75         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.57/0.75          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.57/0.75          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.75  thf('17', plain,
% 0.57/0.75      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.57/0.75        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_3)))),
% 0.57/0.75      inference('sup-', [status(thm)], ['15', '16'])).
% 0.57/0.75  thf('18', plain,
% 0.57/0.75      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(redefinition_k1_relset_1, axiom,
% 0.57/0.75    (![A:$i,B:$i,C:$i]:
% 0.57/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.57/0.75  thf('19', plain,
% 0.57/0.75      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.57/0.75         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.57/0.75          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.57/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.57/0.75  thf('20', plain,
% 0.57/0.75      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.57/0.75  thf('21', plain,
% 0.57/0.75      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.57/0.75        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.57/0.75      inference('demod', [status(thm)], ['17', '20'])).
% 0.57/0.75  thf(zf_stmt_2, axiom,
% 0.57/0.75    (![B:$i,A:$i]:
% 0.57/0.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.75       ( zip_tseitin_0 @ B @ A ) ))).
% 0.57/0.75  thf('22', plain,
% 0.57/0.75      (![X43 : $i, X44 : $i]:
% 0.57/0.75         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.75  thf('23', plain,
% 0.57/0.75      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.57/0.75  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.57/0.75  thf(zf_stmt_5, axiom,
% 0.57/0.75    (![A:$i,B:$i,C:$i]:
% 0.57/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.57/0.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.57/0.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.57/0.75  thf('24', plain,
% 0.57/0.75      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.57/0.75         (~ (zip_tseitin_0 @ X48 @ X49)
% 0.57/0.75          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 0.57/0.75          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.57/0.75  thf('25', plain,
% 0.57/0.75      (((zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.57/0.75        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.57/0.75      inference('sup-', [status(thm)], ['23', '24'])).
% 0.57/0.75  thf('26', plain,
% 0.57/0.75      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A))),
% 0.57/0.75      inference('sup-', [status(thm)], ['22', '25'])).
% 0.57/0.75  thf('27', plain,
% 0.57/0.75      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(cc2_relset_1, axiom,
% 0.57/0.75    (![A:$i,B:$i,C:$i]:
% 0.57/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.57/0.75  thf('28', plain,
% 0.57/0.75      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.57/0.75         ((v5_relat_1 @ X34 @ X36)
% 0.57/0.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.57/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.57/0.75  thf('29', plain, ((v5_relat_1 @ sk_D_3 @ sk_B)),
% 0.57/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.75  thf(d19_relat_1, axiom,
% 0.57/0.75    (![A:$i,B:$i]:
% 0.57/0.75     ( ( v1_relat_1 @ B ) =>
% 0.57/0.75       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.57/0.75  thf('30', plain,
% 0.57/0.75      (![X23 : $i, X24 : $i]:
% 0.57/0.75         (~ (v5_relat_1 @ X23 @ X24)
% 0.57/0.75          | (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.57/0.75          | ~ (v1_relat_1 @ X23))),
% 0.57/0.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.57/0.75  thf('31', plain,
% 0.57/0.75      ((~ (v1_relat_1 @ sk_D_3) | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_B))),
% 0.57/0.75      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.75  thf('32', plain, ((v1_relat_1 @ sk_D_3)),
% 0.57/0.75      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.75  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_B)),
% 0.57/0.75      inference('demod', [status(thm)], ['31', '32'])).
% 0.57/0.75  thf(t12_xboole_1, axiom,
% 0.57/0.75    (![A:$i,B:$i]:
% 0.57/0.75     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.57/0.75  thf('34', plain,
% 0.57/0.75      (![X6 : $i, X7 : $i]:
% 0.57/0.75         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.57/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.57/0.75  thf('35', plain, (((k2_xboole_0 @ (k2_relat_1 @ sk_D_3) @ sk_B) = (sk_B))),
% 0.57/0.75      inference('sup-', [status(thm)], ['33', '34'])).
% 0.57/0.75  thf('36', plain,
% 0.57/0.75      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_3))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf(d3_xboole_0, axiom,
% 0.57/0.75    (![A:$i,B:$i,C:$i]:
% 0.57/0.75     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.57/0.75       ( ![D:$i]:
% 0.57/0.75         ( ( r2_hidden @ D @ C ) <=>
% 0.57/0.75           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.57/0.75  thf('37', plain,
% 0.57/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.57/0.75         (~ (r2_hidden @ X0 @ X3)
% 0.57/0.75          | (r2_hidden @ X0 @ X2)
% 0.57/0.75          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.57/0.75      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.57/0.75  thf('38', plain,
% 0.57/0.75      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.57/0.75         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.57/0.75      inference('simplify', [status(thm)], ['37'])).
% 0.57/0.75  thf('39', plain,
% 0.57/0.75      (![X0 : $i]:
% 0.57/0.75         (r2_hidden @ sk_C_1 @ 
% 0.57/0.75          (k2_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_3) @ X0))),
% 0.57/0.75      inference('sup-', [status(thm)], ['36', '38'])).
% 0.57/0.75  thf('40', plain,
% 0.57/0.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.75  thf('41', plain,
% 0.57/0.75      (![X0 : $i]:
% 0.57/0.75         (r2_hidden @ sk_C_1 @ (k2_xboole_0 @ (k2_relat_1 @ sk_D_3) @ X0))),
% 0.57/0.75      inference('demod', [status(thm)], ['39', '40'])).
% 0.57/0.75  thf('42', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.57/0.75      inference('sup+', [status(thm)], ['35', '41'])).
% 0.57/0.75  thf(t63_subset_1, axiom,
% 0.57/0.75    (![A:$i,B:$i]:
% 0.57/0.75     ( ( r2_hidden @ A @ B ) =>
% 0.57/0.75       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.57/0.75  thf('43', plain,
% 0.57/0.75      (![X16 : $i, X17 : $i]:
% 0.57/0.75         ((m1_subset_1 @ (k1_tarski @ X16) @ (k1_zfmisc_1 @ X17))
% 0.57/0.75          | ~ (r2_hidden @ X16 @ X17))),
% 0.57/0.75      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.57/0.75  thf('44', plain,
% 0.57/0.75      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.57/0.75      inference('sup-', [status(thm)], ['42', '43'])).
% 0.57/0.75  thf(t3_subset, axiom,
% 0.57/0.75    (![A:$i,B:$i]:
% 0.57/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.75  thf('45', plain,
% 0.57/0.75      (![X18 : $i, X19 : $i]:
% 0.57/0.75         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.57/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.75  thf('46', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.57/0.75      inference('sup-', [status(thm)], ['44', '45'])).
% 0.57/0.75  thf('47', plain,
% 0.57/0.75      (![X6 : $i, X7 : $i]:
% 0.57/0.75         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.57/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.57/0.75  thf('48', plain, (((k2_xboole_0 @ (k1_tarski @ sk_C_1) @ sk_B) = (sk_B))),
% 0.57/0.75      inference('sup-', [status(thm)], ['46', '47'])).
% 0.57/0.75  thf(t49_zfmisc_1, axiom,
% 0.57/0.75    (![A:$i,B:$i]:
% 0.57/0.75     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.57/0.75  thf('49', plain,
% 0.57/0.75      (![X14 : $i, X15 : $i]:
% 0.57/0.75         ((k2_xboole_0 @ (k1_tarski @ X14) @ X15) != (k1_xboole_0))),
% 0.57/0.75      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.57/0.75  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 0.57/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.57/0.75  thf('51', plain, ((zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)),
% 0.57/0.75      inference('simplify_reflect-', [status(thm)], ['26', '50'])).
% 0.57/0.75  thf('52', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('demod', [status(thm)], ['21', '51'])).
% 0.57/0.75  thf('53', plain, ((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_D_3) @ sk_A)),
% 0.57/0.75      inference('demod', [status(thm)], ['14', '52'])).
% 0.57/0.75  thf('54', plain,
% 0.57/0.75      (![X51 : $i]:
% 0.57/0.75         (~ (r2_hidden @ X51 @ sk_A)
% 0.57/0.75          | ((k1_funct_1 @ sk_D_3 @ X51) != (sk_C_1)))),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('55', plain,
% 0.57/0.75      (((k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_C_1 @ sk_D_3)) != (sk_C_1))),
% 0.57/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.75  thf('56', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('demod', [status(thm)], ['0', '3'])).
% 0.57/0.75  thf('57', plain,
% 0.57/0.75      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.57/0.75         (((X30) != (k2_relat_1 @ X28))
% 0.57/0.75          | ((X31) = (k1_funct_1 @ X28 @ (sk_D_2 @ X31 @ X28)))
% 0.57/0.75          | ~ (r2_hidden @ X31 @ X30)
% 0.57/0.75          | ~ (v1_funct_1 @ X28)
% 0.57/0.75          | ~ (v1_relat_1 @ X28))),
% 0.57/0.75      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.57/0.75  thf('58', plain,
% 0.57/0.75      (![X28 : $i, X31 : $i]:
% 0.57/0.75         (~ (v1_relat_1 @ X28)
% 0.57/0.75          | ~ (v1_funct_1 @ X28)
% 0.57/0.75          | ~ (r2_hidden @ X31 @ (k2_relat_1 @ X28))
% 0.57/0.75          | ((X31) = (k1_funct_1 @ X28 @ (sk_D_2 @ X31 @ X28))))),
% 0.57/0.75      inference('simplify', [status(thm)], ['57'])).
% 0.57/0.75  thf('59', plain,
% 0.57/0.75      ((((sk_C_1) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_C_1 @ sk_D_3)))
% 0.57/0.75        | ~ (v1_funct_1 @ sk_D_3)
% 0.57/0.75        | ~ (v1_relat_1 @ sk_D_3))),
% 0.57/0.75      inference('sup-', [status(thm)], ['56', '58'])).
% 0.57/0.75  thf('60', plain, ((v1_funct_1 @ sk_D_3)),
% 0.57/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.75  thf('61', plain, ((v1_relat_1 @ sk_D_3)),
% 0.57/0.75      inference('demod', [status(thm)], ['11', '12'])).
% 0.57/0.75  thf('62', plain,
% 0.57/0.75      (((sk_C_1) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_C_1 @ sk_D_3)))),
% 0.57/0.75      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.57/0.75  thf('63', plain, (((sk_C_1) != (sk_C_1))),
% 0.57/0.75      inference('demod', [status(thm)], ['55', '62'])).
% 0.57/0.75  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 0.57/0.75  
% 0.57/0.75  % SZS output end Refutation
% 0.57/0.75  
% 0.57/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
