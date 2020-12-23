%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mIhdjvpz5M

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:16 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 103 expanded)
%              Number of leaves         :   44 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  596 ( 904 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_2 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_1 @ X40 @ X41 )
      | ( zip_tseitin_2 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_1 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ X6 @ X10 )
      | ( X10
       != ( k1_enumset1 @ X9 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k1_enumset1 @ X9 @ X8 @ X7 ) )
      | ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ ( k1_tarski @ X1 ) @ X2 )
      | ( zip_tseitin_0 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('23',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ~ ( zip_tseitin_0 @ X1 @ X3 @ X4 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','25','28'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X22 @ X21 ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mIhdjvpz5M
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:42:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 77 iterations in 0.089s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.35/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(t65_funct_2, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.35/0.54         ( m1_subset_1 @
% 0.35/0.54           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.35/0.54       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.35/0.54            ( m1_subset_1 @
% 0.35/0.54              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.35/0.54          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.35/0.54  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc2_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.35/0.54         ((v5_relat_1 @ X29 @ X31)
% 0.35/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.54  thf('3', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.54  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d1_funct_2, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_1, axiom,
% 0.35/0.54    (![C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.35/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.35/0.54         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.35/0.54          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.35/0.54          | ~ (zip_tseitin_2 @ X39 @ X38 @ X37))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_4, axiom,
% 0.35/0.54    (![B:$i,A:$i]:
% 0.35/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54       ( zip_tseitin_1 @ B @ A ) ))).
% 0.35/0.54  thf(zf_stmt_5, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.35/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.35/0.54         (~ (zip_tseitin_1 @ X40 @ X41)
% 0.35/0.54          | (zip_tseitin_2 @ X42 @ X40 @ X41)
% 0.35/0.54          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.54        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X35 : $i, X36 : $i]:
% 0.35/0.54         ((zip_tseitin_1 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.54  thf('11', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.35/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.35/0.54  thf(t69_enumset1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.35/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.54  thf(t70_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X19 : $i, X20 : $i]:
% 0.35/0.54         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.35/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.54  thf(d1_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.54       ( ![E:$i]:
% 0.35/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.35/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_7, axiom,
% 0.35/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.35/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_8, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.54       ( ![E:$i]:
% 0.35/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.35/0.54          | (r2_hidden @ X6 @ X10)
% 0.35/0.54          | ((X10) != (k1_enumset1 @ X9 @ X8 @ X7)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.54         ((r2_hidden @ X6 @ (k1_enumset1 @ X9 @ X8 @ X7))
% 0.35/0.54          | (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9))),
% 0.35/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.35/0.54  thf(t7_ordinal1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X24 : $i, X25 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.35/0.54          | ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.35/0.54          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['14', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.35/0.54          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['13', '19'])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         ((zip_tseitin_1 @ (k1_tarski @ X1) @ X2)
% 0.35/0.54          | (zip_tseitin_0 @ X0 @ X1 @ X1 @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '20'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.54         (((X2) != (X1)) | ~ (zip_tseitin_0 @ X2 @ X3 @ X4 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X1 : $i, X3 : $i, X4 : $i]: ~ (zip_tseitin_0 @ X1 @ X3 @ X4 @ X1)),
% 0.35/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.35/0.54      inference('sup-', [status(thm)], ['21', '23'])).
% 0.35/0.54  thf('25', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['9', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.35/0.54         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.35/0.54          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.54  thf('29', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['6', '25', '28'])).
% 0.35/0.54  thf(t172_funct_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.54       ( ![C:$i]:
% 0.35/0.54         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.54           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.35/0.54          | (r2_hidden @ (k1_funct_1 @ X22 @ X21) @ X23)
% 0.35/0.54          | ~ (v1_funct_1 @ X22)
% 0.35/0.54          | ~ (v5_relat_1 @ X22 @ X23)
% 0.35/0.54          | ~ (v1_relat_1 @ X22))),
% 0.35/0.54      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.54          | ~ (v1_relat_1 @ sk_D)
% 0.35/0.54          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.35/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.35/0.54          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( v1_relat_1 @ C ) ))).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.54         ((v1_relat_1 @ X26)
% 0.35/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.54  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.54          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.35/0.54          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.35/0.54      inference('demod', [status(thm)], ['31', '34', '35'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.35/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['3', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['0', '37'])).
% 0.35/0.54  thf(d1_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X16 @ X15)
% 0.35/0.54          | ((X16) = (X13))
% 0.35/0.54          | ((X15) != (k1_tarski @ X13)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (![X13 : $i, X16 : $i]:
% 0.35/0.54         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.35/0.54  thf('41', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['38', '40'])).
% 0.35/0.54  thf('42', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('43', plain, ($false),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
