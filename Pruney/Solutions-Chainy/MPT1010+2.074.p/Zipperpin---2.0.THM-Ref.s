%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x8gwZa1dLM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 (  90 expanded)
%              Number of leaves         :   34 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  506 ( 832 expanded)
%              Number of equality atoms :   32 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ X3 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ X0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','17','20'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X18 ) @ X16 )
      | ( X18
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','25','28'])).

thf('30',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9 = X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ ( k1_tarski @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('36',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x8gwZa1dLM
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 82 iterations in 0.103s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(t65_funct_2, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.56       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.56            ( m1_subset_1 @
% 0.21/0.56              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.56          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.56  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d1_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_1, axiom,
% 0.21/0.56    (![C:$i,B:$i,A:$i]:
% 0.21/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.56         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.21/0.56          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.21/0.56          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((~ (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.21/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_4, axiom,
% 0.21/0.56    (![B:$i,A:$i]:
% 0.21/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.56  thf(zf_stmt_5, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.56         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.21/0.56          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.21/0.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.21/0.56        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X25 : $i, X26 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X25 : $i, X26 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.21/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.56  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.56  thf('10', plain, (![X6 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X0)
% 0.21/0.56          | (zip_tseitin_0 @ X0 @ X2)
% 0.21/0.56          | (zip_tseitin_0 @ (k1_tarski @ X1) @ X3))),
% 0.21/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X25 : $i, X26 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.56  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.21/0.56      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ (k1_tarski @ X1) @ X3) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.56      inference('clc', [status(thm)], ['11', '14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ (k1_tarski @ X1) @ X0)),
% 0.21/0.56      inference('condensation', [status(thm)], ['15'])).
% 0.21/0.56  thf('17', plain, ((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.56         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.21/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('21', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '17', '20'])).
% 0.21/0.56  thf(d4_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ![B:$i,C:$i]:
% 0.21/0.56         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.56               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.21/0.56               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.21/0.56          | (r2_hidden @ (k4_tarski @ X15 @ X18) @ X16)
% 0.21/0.56          | ((X18) != (k1_funct_1 @ X16 @ X15))
% 0.21/0.56          | ~ (v1_funct_1 @ X16)
% 0.21/0.56          | ~ (v1_relat_1 @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X16)
% 0.21/0.56          | ~ (v1_funct_1 @ X16)
% 0.21/0.56          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 0.21/0.56          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D)
% 0.21/0.56          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.56          | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '23'])).
% 0.21/0.56  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( v1_relat_1 @ C ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.56         ((v1_relat_1 @ X19)
% 0.21/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.56  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['24', '25', '28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ sk_D)),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ 
% 0.21/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(l3_subset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.56          | (r2_hidden @ X12 @ X14)
% 0.21/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ 
% 0.21/0.56        (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.56  thf(t129_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( r2_hidden @
% 0.21/0.56         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.56       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.56         (((X9) = (X10))
% 0.21/0.56          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ 
% 0.21/0.56               (k2_zfmisc_1 @ X8 @ (k1_tarski @ X10))))),
% 0.21/0.56      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.21/0.56  thf('36', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('38', plain, ($false),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
