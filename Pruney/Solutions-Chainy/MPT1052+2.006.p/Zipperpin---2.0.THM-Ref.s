%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NeXB33bsuU

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:24 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 125 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  533 ( 947 expanded)
%              Number of equality atoms :   34 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t169_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
         => ( ( ( k1_relat_1 @ C )
              = A )
            & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( r2_hidden @ X30 @ ( k1_funct_2 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('2',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( r2_hidden @ X30 @ ( k1_funct_2 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('18',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( zip_tseitin_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,(
    zip_tseitin_0 @ sk_B_1 @ sk_A ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['13','36'])).

thf('38',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['39'])).

thf('49',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['39'])).

thf('51',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['40','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NeXB33bsuU
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:55:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.56/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.75  % Solved by: fo/fo7.sh
% 0.56/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.75  % done 219 iterations in 0.265s
% 0.56/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.75  % SZS output start Refutation
% 0.56/0.75  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.56/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.56/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.56/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.56/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.56/0.75  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.56/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.56/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.56/0.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.56/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.75  thf(t169_funct_2, conjecture,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.75       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.75         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.56/0.75           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.56/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.75        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.75          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.75            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.56/0.75              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.56/0.75    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.56/0.75  thf('0', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(t121_funct_2, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.56/0.75       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.56/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.56/0.75  thf('1', plain,
% 0.56/0.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.56/0.75         ((v1_funct_2 @ X30 @ X31 @ X32)
% 0.56/0.75          | ~ (r2_hidden @ X30 @ (k1_funct_2 @ X31 @ X32)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.56/0.75  thf('2', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.56/0.75      inference('sup-', [status(thm)], ['0', '1'])).
% 0.56/0.75  thf(d1_funct_2, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.56/0.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.56/0.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.56/0.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.56/0.75  thf(zf_stmt_1, axiom,
% 0.56/0.75    (![C:$i,B:$i,A:$i]:
% 0.56/0.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.56/0.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.56/0.75  thf('3', plain,
% 0.56/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.56/0.75         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.56/0.75          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.56/0.75          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.56/0.75  thf('4', plain,
% 0.56/0.75      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.56/0.75        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.75  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('6', plain,
% 0.56/0.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.56/0.75         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.56/0.75          | ~ (r2_hidden @ X30 @ (k1_funct_2 @ X31 @ X32)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.56/0.75  thf('7', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.75  thf(redefinition_k1_relset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.56/0.75  thf('8', plain,
% 0.56/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.56/0.75         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.56/0.75          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.56/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.56/0.75  thf('9', plain,
% 0.56/0.75      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.56/0.75      inference('sup-', [status(thm)], ['7', '8'])).
% 0.56/0.75  thf('10', plain,
% 0.56/0.75      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.56/0.75        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.56/0.75      inference('demod', [status(thm)], ['4', '9'])).
% 0.56/0.75  thf('11', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.75  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.56/0.75  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.56/0.75  thf(zf_stmt_4, axiom,
% 0.56/0.75    (![B:$i,A:$i]:
% 0.56/0.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.75       ( zip_tseitin_0 @ B @ A ) ))).
% 0.56/0.75  thf(zf_stmt_5, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.56/0.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.56/0.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.56/0.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.56/0.75  thf('12', plain,
% 0.56/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.56/0.75         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.56/0.75          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.56/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.56/0.75  thf('13', plain,
% 0.56/0.75      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.56/0.75        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.56/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('14', plain,
% 0.56/0.75      (![X20 : $i, X21 : $i]:
% 0.56/0.75         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.56/0.75  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.56/0.75  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.75      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.75  thf('16', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.56/0.75      inference('sup+', [status(thm)], ['14', '15'])).
% 0.56/0.75  thf(fc3_funct_2, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.56/0.75       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.56/0.75  thf('17', plain,
% 0.56/0.75      (![X28 : $i, X29 : $i]:
% 0.56/0.75         ((v1_xboole_0 @ X28)
% 0.56/0.75          | ~ (v1_xboole_0 @ X29)
% 0.56/0.75          | (v1_xboole_0 @ (k1_funct_2 @ X28 @ X29)))),
% 0.56/0.75      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.56/0.75  thf('18', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(d1_xboole_0, axiom,
% 0.56/0.75    (![A:$i]:
% 0.56/0.75     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.75  thf('19', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.75  thf('20', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.56/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.56/0.75  thf('21', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.56/0.75      inference('sup-', [status(thm)], ['17', '20'])).
% 0.56/0.75  thf('22', plain,
% 0.56/0.75      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_A))),
% 0.56/0.75      inference('sup-', [status(thm)], ['16', '21'])).
% 0.56/0.75  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.75      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.56/0.75  thf(d3_tarski, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.56/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.56/0.75  thf('24', plain,
% 0.56/0.75      (![X4 : $i, X6 : $i]:
% 0.56/0.75         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.56/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.75  thf('25', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.75  thf('26', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.56/0.75  thf('27', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.56/0.75  thf(d10_xboole_0, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.56/0.75  thf('28', plain,
% 0.56/0.75      (![X7 : $i, X9 : $i]:
% 0.56/0.75         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.56/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.56/0.75  thf('29', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.56/0.75  thf('30', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['26', '29'])).
% 0.56/0.75  thf('31', plain,
% 0.56/0.75      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['23', '30'])).
% 0.56/0.75  thf('32', plain,
% 0.56/0.75      (![X20 : $i, X21 : $i]:
% 0.56/0.75         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.56/0.75  thf('33', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.56/0.75      inference('simplify', [status(thm)], ['32'])).
% 0.56/0.75  thf('34', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['31', '33'])).
% 0.56/0.75  thf('35', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((zip_tseitin_0 @ sk_B_1 @ X1) | (zip_tseitin_0 @ X0 @ sk_A))),
% 0.56/0.75      inference('sup-', [status(thm)], ['22', '34'])).
% 0.56/0.75  thf('36', plain, ((zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.56/0.75      inference('eq_fact', [status(thm)], ['35'])).
% 0.56/0.75  thf('37', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.56/0.75      inference('demod', [status(thm)], ['13', '36'])).
% 0.56/0.75  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.56/0.75      inference('demod', [status(thm)], ['10', '37'])).
% 0.56/0.75  thf('39', plain,
% 0.56/0.75      ((((k1_relat_1 @ sk_C_1) != (sk_A))
% 0.56/0.75        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('40', plain,
% 0.56/0.75      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 0.56/0.75         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.56/0.75      inference('split', [status(esa)], ['39'])).
% 0.56/0.75  thf('41', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.56/0.75  thf(cc2_relset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.56/0.75  thf('42', plain,
% 0.56/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.56/0.75         ((v5_relat_1 @ X14 @ X16)
% 0.56/0.75          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.56/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.75  thf('43', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.56/0.75      inference('sup-', [status(thm)], ['41', '42'])).
% 0.56/0.75  thf(d19_relat_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( v1_relat_1 @ B ) =>
% 0.56/0.75       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.56/0.75  thf('44', plain,
% 0.56/0.75      (![X12 : $i, X13 : $i]:
% 0.56/0.75         (~ (v5_relat_1 @ X12 @ X13)
% 0.56/0.75          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.56/0.75          | ~ (v1_relat_1 @ X12))),
% 0.56/0.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.56/0.75  thf('45', plain,
% 0.56/0.75      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.56/0.75      inference('sup-', [status(thm)], ['43', '44'])).
% 0.56/0.75  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.56/0.75      inference('demod', [status(thm)], ['45', '46'])).
% 0.56/0.75  thf('48', plain,
% 0.56/0.75      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))
% 0.56/0.75         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.56/0.75      inference('split', [status(esa)], ['39'])).
% 0.56/0.75  thf('49', plain, (((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.56/0.75      inference('sup-', [status(thm)], ['47', '48'])).
% 0.56/0.75  thf('50', plain,
% 0.56/0.75      (~ (((k1_relat_1 @ sk_C_1) = (sk_A))) | 
% 0.56/0.75       ~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.56/0.75      inference('split', [status(esa)], ['39'])).
% 0.56/0.75  thf('51', plain, (~ (((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 0.56/0.75      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.56/0.75  thf('52', plain, (((k1_relat_1 @ sk_C_1) != (sk_A))),
% 0.56/0.75      inference('simpl_trail', [status(thm)], ['40', '51'])).
% 0.56/0.75  thf('53', plain, ($false),
% 0.56/0.75      inference('simplify_reflect-', [status(thm)], ['38', '52'])).
% 0.56/0.75  
% 0.56/0.75  % SZS output end Refutation
% 0.56/0.75  
% 0.56/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
