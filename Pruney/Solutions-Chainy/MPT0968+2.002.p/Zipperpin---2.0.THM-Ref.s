%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ZuLWmILwK

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:15 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 276 expanded)
%              Number of leaves         :   47 ( 101 expanded)
%              Depth                    :   24
%              Number of atoms          : 1041 (2503 expanded)
%              Number of equality atoms :   99 ( 228 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['7','8'])).

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
      ( ( zip_tseitin_2 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf('10',plain,(
    ! [X43: $i,X44: $i,X45: $i,X47: $i] :
      ( ( zip_tseitin_2 @ X43 @ X45 @ X44 @ X47 )
      | ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_funct_1 @ X43 )
      | ( X45 != X43 )
      | ( ( k1_relat_1 @ X43 )
       != X47 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X43 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X43 ) @ X44 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 )
      | ( zip_tseitin_2 @ X43 @ X43 @ X44 @ ( k1_relat_1 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_C @ sk_B_1 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B_1 @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_B @ X0 ) @ X0 )
      = ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( v1_xboole_0 @ ( sk_B @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ( X6 = X7 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('43',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('44',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X43 ) @ X44 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 )
      | ( zip_tseitin_2 @ X43 @ X43 @ X44 @ ( k1_relat_1 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('47',plain,(
    ! [X8: $i] :
      ( v1_xboole_0 @ ( sk_B @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','33'])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ( X6 = X7 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t25_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X33: $i,X34: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t25_relset_1])).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('58',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('60',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','52','53','56','65'])).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( zip_tseitin_2 @ X48 @ X49 @ X50 @ X51 )
      | ( r2_hidden @ X49 @ X52 )
      | ( X52
       != ( k1_funct_2 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('68',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ X49 @ ( k1_funct_2 @ X51 @ X50 ) )
      | ~ ( zip_tseitin_2 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('71',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_funct_2 @ k1_xboole_0 @ sk_B_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('82',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('85',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('86',plain,
    ( ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('88',plain,(
    ! [X35: $i] :
      ( zip_tseitin_0 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','88'])).

thf('90',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','89'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('92',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( sk_C = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('94',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k1_funct_2 @ k1_xboole_0 @ sk_B_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','95'])).

thf('97',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','96'])).

thf('98',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('99',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('100',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','100'])).

thf('102',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','33'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['102','103'])).

thf('105',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['39','104'])).

thf('106',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','105'])).

thf('107',plain,(
    zip_tseitin_2 @ sk_C @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['17','106'])).

thf('108',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ X49 @ ( k1_funct_2 @ X51 @ X50 ) )
      | ~ ( zip_tseitin_2 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('109',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ZuLWmILwK
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 20:29:41 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.70/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.92  % Solved by: fo/fo7.sh
% 0.70/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.92  % done 637 iterations in 0.458s
% 0.70/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.92  % SZS output start Refutation
% 0.70/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.92  thf(sk_B_type, type, sk_B: $i > $i).
% 0.70/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.70/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.92  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.70/0.92  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.70/0.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.70/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.70/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.70/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.70/0.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.70/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.92  thf(t11_funct_2, conjecture,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.92         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.70/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.92        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.92            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.92          ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.92            ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )),
% 0.70/0.92    inference('cnf.neg', [status(esa)], [t11_funct_2])).
% 0.70/0.92  thf('0', plain, (~ (r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('1', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(dt_k2_relset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.70/0.92  thf('2', plain,
% 0.70/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.70/0.92         ((m1_subset_1 @ (k2_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))
% 0.70/0.92          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.70/0.92  thf('3', plain,
% 0.70/0.92      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) @ 
% 0.70/0.92        (k1_zfmisc_1 @ sk_B_1))),
% 0.70/0.92      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.92  thf('4', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(redefinition_k2_relset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.70/0.92  thf('5', plain,
% 0.70/0.92      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.70/0.92         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.70/0.92          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.70/0.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.70/0.92  thf('6', plain,
% 0.70/0.92      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.70/0.92      inference('sup-', [status(thm)], ['4', '5'])).
% 0.70/0.92  thf('7', plain,
% 0.70/0.92      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.70/0.92      inference('demod', [status(thm)], ['3', '6'])).
% 0.70/0.92  thf(t3_subset, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.92  thf('8', plain,
% 0.70/0.92      (![X9 : $i, X10 : $i]:
% 0.70/0.92         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.92  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 0.70/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.92  thf(d2_funct_2, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.70/0.92       ( ![D:$i]:
% 0.70/0.92         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.92           ( ?[E:$i]:
% 0.70/0.92             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.70/0.92               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.70/0.92               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.70/0.92  thf(zf_stmt_1, axiom,
% 0.70/0.92    (![E:$i,D:$i,B:$i,A:$i]:
% 0.70/0.92     ( ( zip_tseitin_2 @ E @ D @ B @ A ) <=>
% 0.70/0.92       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.70/0.92         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.70/0.92         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.70/0.92  thf('10', plain,
% 0.70/0.92      (![X43 : $i, X44 : $i, X45 : $i, X47 : $i]:
% 0.70/0.92         ((zip_tseitin_2 @ X43 @ X45 @ X44 @ X47)
% 0.70/0.92          | ~ (v1_relat_1 @ X43)
% 0.70/0.92          | ~ (v1_funct_1 @ X43)
% 0.70/0.92          | ((X45) != (X43))
% 0.70/0.92          | ((k1_relat_1 @ X43) != (X47))
% 0.70/0.92          | ~ (r1_tarski @ (k2_relat_1 @ X43) @ X44))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.70/0.92  thf('11', plain,
% 0.70/0.92      (![X43 : $i, X44 : $i]:
% 0.70/0.92         (~ (r1_tarski @ (k2_relat_1 @ X43) @ X44)
% 0.70/0.92          | ~ (v1_funct_1 @ X43)
% 0.70/0.92          | ~ (v1_relat_1 @ X43)
% 0.70/0.92          | (zip_tseitin_2 @ X43 @ X43 @ X44 @ (k1_relat_1 @ X43)))),
% 0.70/0.92      inference('simplify', [status(thm)], ['10'])).
% 0.70/0.92  thf('12', plain,
% 0.70/0.92      (((zip_tseitin_2 @ sk_C @ sk_C @ sk_B_1 @ (k1_relat_1 @ sk_C))
% 0.70/0.92        | ~ (v1_relat_1 @ sk_C)
% 0.70/0.92        | ~ (v1_funct_1 @ sk_C))),
% 0.70/0.92      inference('sup-', [status(thm)], ['9', '11'])).
% 0.70/0.92  thf('13', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(cc1_relset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( v1_relat_1 @ C ) ))).
% 0.70/0.92  thf('14', plain,
% 0.70/0.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.92         ((v1_relat_1 @ X18)
% 0.70/0.92          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.70/0.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.70/0.92  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.70/0.92      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.92  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('17', plain,
% 0.70/0.92      ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B_1 @ (k1_relat_1 @ sk_C))),
% 0.70/0.92      inference('demod', [status(thm)], ['12', '15', '16'])).
% 0.70/0.92  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(d1_funct_2, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.70/0.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.70/0.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.70/0.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.70/0.92  thf(zf_stmt_2, axiom,
% 0.70/0.92    (![C:$i,B:$i,A:$i]:
% 0.70/0.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.70/0.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.70/0.92  thf('19', plain,
% 0.70/0.92      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.70/0.92         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.70/0.92          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.70/0.92          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.92  thf('20', plain,
% 0.70/0.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.70/0.92        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['18', '19'])).
% 0.70/0.92  thf('21', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(redefinition_k1_relset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.70/0.92  thf('22', plain,
% 0.70/0.92      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.70/0.92         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.70/0.92          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.70/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.92  thf('23', plain,
% 0.70/0.92      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.70/0.92      inference('sup-', [status(thm)], ['21', '22'])).
% 0.70/0.92  thf('24', plain,
% 0.70/0.92      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.70/0.92        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.70/0.92      inference('demod', [status(thm)], ['20', '23'])).
% 0.70/0.92  thf(zf_stmt_3, axiom,
% 0.70/0.92    (![B:$i,A:$i]:
% 0.70/0.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.92       ( zip_tseitin_0 @ B @ A ) ))).
% 0.70/0.92  thf('25', plain,
% 0.70/0.92      (![X35 : $i, X36 : $i]:
% 0.70/0.92         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.70/0.92  thf(rc2_subset_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ?[B:$i]:
% 0.70/0.92       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.70/0.92  thf('26', plain,
% 0.70/0.92      (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.70/0.92      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.70/0.92  thf('27', plain,
% 0.70/0.92      (![X9 : $i, X10 : $i]:
% 0.70/0.92         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.92  thf('28', plain, (![X0 : $i]: (r1_tarski @ (sk_B @ X0) @ X0)),
% 0.70/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.70/0.92  thf(t28_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.92  thf('29', plain,
% 0.70/0.92      (![X3 : $i, X4 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.70/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.92  thf('30', plain,
% 0.70/0.92      (![X0 : $i]: ((k3_xboole_0 @ (sk_B @ X0) @ X0) = (sk_B @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['28', '29'])).
% 0.70/0.92  thf(t2_boole, axiom,
% 0.70/0.92    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.70/0.92  thf('31', plain,
% 0.70/0.92      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('cnf', [status(esa)], [t2_boole])).
% 0.70/0.92  thf('32', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['30', '31'])).
% 0.70/0.92  thf('33', plain, (![X8 : $i]: (v1_xboole_0 @ (sk_B @ X8))),
% 0.70/0.92      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.70/0.92  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('sup+', [status(thm)], ['32', '33'])).
% 0.70/0.92  thf('35', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.70/0.92      inference('sup+', [status(thm)], ['25', '34'])).
% 0.70/0.92  thf('36', plain,
% 0.70/0.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.70/0.92  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $o).
% 0.70/0.92  thf(zf_stmt_6, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.70/0.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.70/0.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.70/0.92  thf('37', plain,
% 0.70/0.92      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.70/0.92         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.70/0.92          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.70/0.92          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.70/0.92  thf('38', plain,
% 0.70/0.92      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.70/0.92        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['36', '37'])).
% 0.70/0.92  thf('39', plain,
% 0.70/0.92      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['35', '38'])).
% 0.70/0.92  thf(t8_boole, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.70/0.92  thf('40', plain,
% 0.70/0.92      (![X6 : $i, X7 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ X6) | ~ (v1_xboole_0 @ X7) | ((X6) = (X7)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t8_boole])).
% 0.70/0.92  thf('41', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('42', plain,
% 0.70/0.92      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.70/0.92      inference('split', [status(esa)], ['41'])).
% 0.70/0.92  thf(t60_relat_1, axiom,
% 0.70/0.92    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.70/0.92     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.70/0.92  thf('43', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.70/0.92  thf('44', plain,
% 0.70/0.92      (![X43 : $i, X44 : $i]:
% 0.70/0.92         (~ (r1_tarski @ (k2_relat_1 @ X43) @ X44)
% 0.70/0.92          | ~ (v1_funct_1 @ X43)
% 0.70/0.92          | ~ (v1_relat_1 @ X43)
% 0.70/0.92          | (zip_tseitin_2 @ X43 @ X43 @ X44 @ (k1_relat_1 @ X43)))),
% 0.70/0.92      inference('simplify', [status(thm)], ['10'])).
% 0.70/0.92  thf('45', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.70/0.92          | (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ 
% 0.70/0.92             (k1_relat_1 @ k1_xboole_0))
% 0.70/0.92          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['43', '44'])).
% 0.70/0.92  thf('46', plain, (![X0 : $i]: (r1_tarski @ (sk_B @ X0) @ X0)),
% 0.70/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.70/0.92  thf('47', plain, (![X8 : $i]: (v1_xboole_0 @ (sk_B @ X8))),
% 0.70/0.92      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.70/0.92  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('sup+', [status(thm)], ['32', '33'])).
% 0.70/0.92  thf('49', plain,
% 0.70/0.92      (![X6 : $i, X7 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ X6) | ~ (v1_xboole_0 @ X7) | ((X6) = (X7)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t8_boole])).
% 0.70/0.92  thf('50', plain,
% 0.70/0.92      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['48', '49'])).
% 0.70/0.92  thf('51', plain, (![X0 : $i]: ((k1_xboole_0) = (sk_B @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['47', '50'])).
% 0.70/0.92  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.70/0.92      inference('demod', [status(thm)], ['46', '51'])).
% 0.70/0.92  thf('53', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.70/0.92  thf(t25_relset_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.70/0.92  thf('54', plain,
% 0.70/0.93      (![X33 : $i, X34 : $i]:
% 0.70/0.93         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 0.70/0.93      inference('cnf', [status(esa)], [t25_relset_1])).
% 0.70/0.93  thf('55', plain,
% 0.70/0.93      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.93         ((v1_relat_1 @ X18)
% 0.70/0.93          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.70/0.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.70/0.93  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.70/0.93      inference('sup-', [status(thm)], ['54', '55'])).
% 0.70/0.93  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.70/0.93      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.93  thf('58', plain,
% 0.70/0.93      (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.70/0.93      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.70/0.93  thf('59', plain, (![X0 : $i]: ((k1_xboole_0) = (sk_B @ X0))),
% 0.70/0.93      inference('sup-', [status(thm)], ['47', '50'])).
% 0.70/0.93  thf('60', plain,
% 0.70/0.93      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.70/0.93      inference('demod', [status(thm)], ['58', '59'])).
% 0.70/0.93  thf(cc3_funct_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.93       ( ![B:$i]:
% 0.70/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 0.70/0.93  thf('61', plain,
% 0.70/0.93      (![X16 : $i, X17 : $i]:
% 0.70/0.93         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.70/0.93          | (v1_funct_1 @ X16)
% 0.70/0.93          | ~ (v1_funct_1 @ X17)
% 0.70/0.93          | ~ (v1_relat_1 @ X17))),
% 0.70/0.93      inference('cnf', [status(esa)], [cc3_funct_1])).
% 0.70/0.93  thf('62', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (~ (v1_relat_1 @ X0)
% 0.70/0.93          | ~ (v1_funct_1 @ X0)
% 0.70/0.93          | (v1_funct_1 @ k1_xboole_0))),
% 0.70/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.70/0.93  thf('63', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_funct_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['57', '62'])).
% 0.70/0.93  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('65', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.70/0.93      inference('demod', [status(thm)], ['63', '64'])).
% 0.70/0.93  thf('66', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.70/0.93      inference('demod', [status(thm)], ['45', '52', '53', '56', '65'])).
% 0.70/0.93  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.70/0.93  thf(zf_stmt_8, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.70/0.93       ( ![D:$i]:
% 0.70/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.93           ( ?[E:$i]: ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) ) ))).
% 0.70/0.93  thf('67', plain,
% 0.70/0.93      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.70/0.93         (~ (zip_tseitin_2 @ X48 @ X49 @ X50 @ X51)
% 0.70/0.93          | (r2_hidden @ X49 @ X52)
% 0.70/0.93          | ((X52) != (k1_funct_2 @ X51 @ X50)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.70/0.93  thf('68', plain,
% 0.70/0.93      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.70/0.93         ((r2_hidden @ X49 @ (k1_funct_2 @ X51 @ X50))
% 0.70/0.93          | ~ (zip_tseitin_2 @ X48 @ X49 @ X50 @ X51))),
% 0.70/0.93      inference('simplify', [status(thm)], ['67'])).
% 0.70/0.93  thf('69', plain,
% 0.70/0.93      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ X0))),
% 0.70/0.93      inference('sup-', [status(thm)], ['66', '68'])).
% 0.70/0.93  thf('70', plain,
% 0.70/0.93      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('split', [status(esa)], ['41'])).
% 0.70/0.93  thf('71', plain, (~ (r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('72', plain,
% 0.70/0.93      ((~ (r2_hidden @ sk_C @ (k1_funct_2 @ k1_xboole_0 @ sk_B_1)))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['70', '71'])).
% 0.70/0.93  thf('73', plain,
% 0.70/0.93      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('split', [status(esa)], ['41'])).
% 0.70/0.93  thf('74', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('75', plain,
% 0.70/0.93      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B_1))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('sup+', [status(thm)], ['73', '74'])).
% 0.70/0.93  thf('76', plain,
% 0.70/0.93      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.70/0.93         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.70/0.93          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.70/0.93          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.93  thf('77', plain,
% 0.70/0.93      (((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0)
% 0.70/0.93         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C))))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['75', '76'])).
% 0.70/0.93  thf('78', plain,
% 0.70/0.93      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('split', [status(esa)], ['41'])).
% 0.70/0.93  thf('79', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('80', plain,
% 0.70/0.93      (((m1_subset_1 @ sk_C @ 
% 0.70/0.93         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('sup+', [status(thm)], ['78', '79'])).
% 0.70/0.93  thf('81', plain,
% 0.70/0.93      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.70/0.93         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.70/0.93          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.93  thf('82', plain,
% 0.70/0.93      ((((k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C)))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['80', '81'])).
% 0.70/0.93  thf('83', plain,
% 0.70/0.93      (((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0)
% 0.70/0.93         | ((k1_xboole_0) = (k1_relat_1 @ sk_C))))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('demod', [status(thm)], ['77', '82'])).
% 0.70/0.93  thf('84', plain,
% 0.70/0.93      (((m1_subset_1 @ sk_C @ 
% 0.70/0.93         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('sup+', [status(thm)], ['78', '79'])).
% 0.70/0.93  thf('85', plain,
% 0.70/0.93      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.70/0.93         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.70/0.93          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.70/0.93          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.70/0.93  thf('86', plain,
% 0.70/0.93      ((((zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0)
% 0.70/0.93         | ~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['84', '85'])).
% 0.70/0.93  thf('87', plain,
% 0.70/0.93      (![X35 : $i, X36 : $i]:
% 0.70/0.93         ((zip_tseitin_0 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.70/0.93  thf('88', plain, (![X35 : $i]: (zip_tseitin_0 @ X35 @ k1_xboole_0)),
% 0.70/0.93      inference('simplify', [status(thm)], ['87'])).
% 0.70/0.93  thf('89', plain,
% 0.70/0.93      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ k1_xboole_0))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('demod', [status(thm)], ['86', '88'])).
% 0.70/0.93  thf('90', plain,
% 0.70/0.93      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('demod', [status(thm)], ['83', '89'])).
% 0.70/0.93  thf(t64_relat_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( v1_relat_1 @ A ) =>
% 0.70/0.93       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.70/0.93           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.93         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.70/0.93  thf('91', plain,
% 0.70/0.93      (![X14 : $i]:
% 0.70/0.93         (((k1_relat_1 @ X14) != (k1_xboole_0))
% 0.70/0.93          | ((X14) = (k1_xboole_0))
% 0.70/0.93          | ~ (v1_relat_1 @ X14))),
% 0.70/0.93      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.70/0.93  thf('92', plain,
% 0.70/0.93      (((((k1_xboole_0) != (k1_xboole_0))
% 0.70/0.93         | ~ (v1_relat_1 @ sk_C)
% 0.70/0.93         | ((sk_C) = (k1_xboole_0)))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['90', '91'])).
% 0.70/0.93  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.70/0.93      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.93  thf('94', plain,
% 0.70/0.93      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0))))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('demod', [status(thm)], ['92', '93'])).
% 0.70/0.93  thf('95', plain,
% 0.70/0.93      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('simplify', [status(thm)], ['94'])).
% 0.70/0.93  thf('96', plain,
% 0.70/0.93      ((~ (r2_hidden @ k1_xboole_0 @ (k1_funct_2 @ k1_xboole_0 @ sk_B_1)))
% 0.70/0.93         <= ((((sk_A) = (k1_xboole_0))))),
% 0.70/0.93      inference('demod', [status(thm)], ['72', '95'])).
% 0.70/0.93  thf('97', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['69', '96'])).
% 0.70/0.93  thf('98', plain,
% 0.70/0.93      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.70/0.93      inference('split', [status(esa)], ['41'])).
% 0.70/0.93  thf('99', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.70/0.93      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 0.70/0.93  thf('100', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.70/0.93      inference('simpl_trail', [status(thm)], ['42', '99'])).
% 0.70/0.93  thf('101', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (((X0) != (k1_xboole_0))
% 0.70/0.93          | ~ (v1_xboole_0 @ X0)
% 0.70/0.93          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.70/0.93      inference('sup-', [status(thm)], ['40', '100'])).
% 0.70/0.93  thf('102', plain,
% 0.70/0.93      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.70/0.93      inference('simplify', [status(thm)], ['101'])).
% 0.70/0.93  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.93      inference('sup+', [status(thm)], ['32', '33'])).
% 0.70/0.93  thf('104', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.70/0.93      inference('simplify_reflect+', [status(thm)], ['102', '103'])).
% 0.70/0.93  thf('105', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.70/0.93      inference('clc', [status(thm)], ['39', '104'])).
% 0.70/0.93  thf('106', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.70/0.93      inference('demod', [status(thm)], ['24', '105'])).
% 0.70/0.93  thf('107', plain, ((zip_tseitin_2 @ sk_C @ sk_C @ sk_B_1 @ sk_A)),
% 0.70/0.93      inference('demod', [status(thm)], ['17', '106'])).
% 0.70/0.93  thf('108', plain,
% 0.70/0.93      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.70/0.93         ((r2_hidden @ X49 @ (k1_funct_2 @ X51 @ X50))
% 0.70/0.93          | ~ (zip_tseitin_2 @ X48 @ X49 @ X50 @ X51))),
% 0.70/0.93      inference('simplify', [status(thm)], ['67'])).
% 0.70/0.93  thf('109', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.70/0.93      inference('sup-', [status(thm)], ['107', '108'])).
% 0.70/0.93  thf('110', plain, ($false), inference('demod', [status(thm)], ['0', '109'])).
% 0.70/0.93  
% 0.70/0.93  % SZS output end Refutation
% 0.70/0.93  
% 0.76/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
