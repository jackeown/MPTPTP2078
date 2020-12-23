%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fpsTjuTs1Y

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:21 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   73 (  87 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  506 ( 814 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','15','18'])).

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

thf('20',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X23 ) @ X21 )
      | ( X23
       != ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( k1_funct_1 @ X21 @ X20 ) ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) ) @ sk_D ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14 = X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ ( k1_tarski @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('34',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fpsTjuTs1Y
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 136 iterations in 0.105s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(t65_funct_2, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.38/0.56         ( m1_subset_1 @
% 0.38/0.56           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.38/0.56       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.38/0.56            ( m1_subset_1 @
% 0.38/0.56              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.38/0.56          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.38/0.56  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d1_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_1, axiom,
% 0.38/0.56    (![C:$i,B:$i,A:$i]:
% 0.38/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.56         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.38/0.56          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.38/0.56          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      ((~ (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.38/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_4, axiom,
% 0.38/0.56    (![B:$i,A:$i]:
% 0.38/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.56  thf(zf_stmt_5, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.56         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.38/0.56          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.38/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.38/0.56        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i]:
% 0.38/0.56         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.56  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.38/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf(d1_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         (((X2) != (X1)) | (r2_hidden @ X2 @ X3) | ((X3) != (k1_tarski @ X1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.56  thf('11', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.38/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.56  thf(t7_ordinal1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X24 : $i, X25 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.56  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ (k1_tarski @ X0) @ X1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '13'])).
% 0.38/0.56  thf('15', plain, ((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['6', '14'])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.38/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.56  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.56      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.38/0.56  thf(d4_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ![B:$i,C:$i]:
% 0.38/0.56         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.38/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.38/0.56               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.56           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.38/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.38/0.56               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X20 @ X23) @ X21)
% 0.38/0.56          | ((X23) != (k1_funct_1 @ X21 @ X20))
% 0.38/0.56          | ~ (v1_funct_1 @ X21)
% 0.38/0.56          | ~ (v1_relat_1 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X21)
% 0.38/0.56          | ~ (v1_funct_1 @ X21)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X20 @ (k1_funct_1 @ X21 @ X20)) @ X21)
% 0.38/0.56          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X21)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_D)
% 0.38/0.56          | ~ (v1_relat_1 @ sk_D))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '21'])).
% 0.38/0.56  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( v1_relat_1 @ C ) ))).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.56         ((v1_relat_1 @ X26)
% 0.38/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.56  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D))),
% 0.38/0.56      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      ((r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D @ sk_C_1)) @ sk_D)),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(l3_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X17 @ X18)
% 0.38/0.56          | (r2_hidden @ X17 @ X19)
% 0.38/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.38/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.38/0.56          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.38/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D @ sk_C_1)) @ 
% 0.38/0.56        (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['28', '31'])).
% 0.38/0.56  thf(t129_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( r2_hidden @
% 0.38/0.56         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.38/0.56       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.56         (((X14) = (X15))
% 0.38/0.56          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ 
% 0.38/0.56               (k2_zfmisc_1 @ X13 @ (k1_tarski @ X15))))),
% 0.38/0.56      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.38/0.56  thf('34', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('35', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('36', plain, ($false),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
