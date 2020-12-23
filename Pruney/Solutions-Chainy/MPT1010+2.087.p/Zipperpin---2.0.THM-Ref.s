%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dyNnXRPnnb

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:25 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 123 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  612 (1161 expanded)
%              Number of equality atoms :   51 (  92 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v5_relat_1 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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

thf('5',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ( X44
        = ( k1_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( zip_tseitin_1 @ X46 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_zfmisc_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,(
    ! [X22: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X22 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X24 ) @ X23 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('15',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( zip_tseitin_0 @ X47 @ X48 )
      | ( zip_tseitin_1 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      | ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k1_relset_1 @ X40 @ X41 @ X39 )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','23','26'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X32 @ X31 ) @ X33 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D_1 @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','37'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('42',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('47',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dyNnXRPnnb
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 175 iterations in 0.215s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.67  thf(t65_funct_2, conjecture,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.45/0.67         ( m1_subset_1 @
% 0.45/0.67           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.45/0.67       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.45/0.67            ( m1_subset_1 @
% 0.45/0.67              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.45/0.67          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(cc2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.67         ((v5_relat_1 @ X36 @ X38)
% 0.45/0.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.67  thf('2', plain, ((v5_relat_1 @ sk_D_1 @ (k1_tarski @ sk_B_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.67  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(d1_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_1, axiom,
% 0.45/0.67    (![C:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.67         (~ (v1_funct_2 @ X46 @ X44 @ X45)
% 0.45/0.67          | ((X44) = (k1_relset_1 @ X44 @ X45 @ X46))
% 0.45/0.67          | ~ (zip_tseitin_1 @ X46 @ X45 @ X44))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      ((~ (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.45/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf(zf_stmt_2, axiom,
% 0.45/0.67    (![B:$i,A:$i]:
% 0.45/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X42 : $i, X43 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ X42 @ X43) | ((X42) = (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.67  thf(t113_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i]:
% 0.45/0.67         (((k2_zfmisc_1 @ X21 @ X22) = (k1_xboole_0))
% 0.45/0.67          | ((X21) != (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X22 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X22) = (k1_xboole_0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['8'])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.45/0.67      inference('sup+', [status(thm)], ['7', '9'])).
% 0.45/0.67  thf(t130_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.45/0.67       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.67         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X23 : $i, X24 : $i]:
% 0.45/0.67         (((X23) = (k1_xboole_0))
% 0.45/0.67          | ((k2_zfmisc_1 @ (k1_tarski @ X24) @ X23) != (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.67          | (zip_tseitin_0 @ (k1_tarski @ X1) @ X2)
% 0.45/0.67          | ((X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0)) | (zip_tseitin_0 @ (k1_tarski @ X1) @ X2))),
% 0.45/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_5, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.45/0.67         (~ (zip_tseitin_0 @ X47 @ X48)
% 0.45/0.67          | (zip_tseitin_1 @ X49 @ X47 @ X48)
% 0.45/0.67          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (((zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.45/0.67        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0))
% 0.45/0.67          | (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((X0) = (k1_xboole_0))
% 0.45/0.67          | (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '16'])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((X1) = (X0))
% 0.45/0.67          | (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.45/0.67          | (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.45/0.67          | ((X1) = (X0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf('21', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((X0) != (sk_B_1))
% 0.45/0.67          | (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain, ((zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.45/0.67      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.67         (((k1_relset_1 @ X40 @ X41 @ X39) = (k1_relat_1 @ X39))
% 0.45/0.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_1)
% 0.45/0.67         = (k1_relat_1 @ sk_D_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.67      inference('demod', [status(thm)], ['6', '23', '26'])).
% 0.45/0.67  thf(t176_funct_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.67       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.45/0.67         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 0.45/0.67          | (m1_subset_1 @ (k1_funct_1 @ X32 @ X31) @ X33)
% 0.45/0.67          | ~ (v1_funct_1 @ X32)
% 0.45/0.67          | ~ (v5_relat_1 @ X32 @ X33)
% 0.45/0.67          | ~ (v1_relat_1 @ X32))),
% 0.45/0.67      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.67          | ~ (v1_relat_1 @ sk_D_1)
% 0.45/0.67          | ~ (v5_relat_1 @ sk_D_1 @ X1)
% 0.45/0.67          | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.67          | (m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(cc2_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.45/0.67          | (v1_relat_1 @ X27)
% 0.45/0.67          | ~ (v1_relat_1 @ X28))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.45/0.67        | (v1_relat_1 @ sk_D_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.67  thf(fc6_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X29 : $i, X30 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X29 @ X30))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.67  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.67      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.67  thf('35', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.67          | ~ (v5_relat_1 @ sk_D_1 @ X1)
% 0.45/0.67          | (m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1))),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '34', '35'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ X0)
% 0.45/0.67          | ~ (v5_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['3', '36'])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      ((m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '37'])).
% 0.45/0.67  thf(t2_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X25 : $i, X26 : $i]:
% 0.45/0.67         ((r2_hidden @ X25 @ X26)
% 0.45/0.67          | (v1_xboole_0 @ X26)
% 0.45/0.67          | ~ (m1_subset_1 @ X25 @ X26))),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.45/0.67        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.67  thf(d1_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.67         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.67  thf('42', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.45/0.67      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.67  thf(d1_xboole_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.67  thf('44', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.45/0.67      inference('clc', [status(thm)], ['40', '44'])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      (![X6 : $i, X9 : $i]:
% 0.45/0.67         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.67  thf('48', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['45', '47'])).
% 0.45/0.67  thf('49', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('50', plain, ($false),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
