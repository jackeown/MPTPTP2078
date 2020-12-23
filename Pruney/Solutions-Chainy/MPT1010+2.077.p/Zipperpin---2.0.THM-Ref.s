%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A6gtbRvqFC

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:24 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   83 (  98 expanded)
%              Number of leaves         :   40 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  573 ( 888 expanded)
%              Number of equality atoms :   48 (  63 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( v1_funct_2 @ X61 @ X59 @ X60 )
      | ( X59
        = ( k1_relset_1 @ X59 @ X60 @ X61 ) )
      | ~ ( zip_tseitin_1 @ X61 @ X60 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X57: $i,X58: $i] :
      ( ( zip_tseitin_0 @ X57 @ X58 )
      | ( X57 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('6',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( zip_tseitin_0 @ X62 @ X63 )
      | ( zip_tseitin_1 @ X64 @ X62 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 != X37 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X37: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) )
     != ( k1_tarski @ X37 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k6_subset_1 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X37: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X37 ) ) ),
    inference(demod,[status(thm)],['10','11','18'])).

thf('20',plain,(
    zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['8','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( ( k1_relset_1 @ X55 @ X56 @ X54 )
        = ( k1_relat_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','20','23'])).

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

thf('25',plain,(
    ! [X47: $i,X48: $i,X50: $i] :
      ( ~ ( r2_hidden @ X47 @ ( k1_relat_1 @ X48 ) )
      | ( r2_hidden @ ( k4_tarski @ X47 @ X50 ) @ X48 )
      | ( X50
       != ( k1_funct_1 @ X48 @ X47 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('26',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_funct_1 @ X48 )
      | ( r2_hidden @ ( k4_tarski @ X47 @ ( k1_funct_1 @ X48 @ X47 ) ) @ X48 )
      | ~ ( r2_hidden @ X47 @ ( k1_relat_1 @ X48 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( v1_relat_1 @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','28','31'])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('38',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X35 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ ( k1_tarski @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('39',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A6gtbRvqFC
% 0.13/0.37  % Computer   : n006.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:57:38 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 115 iterations in 0.053s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
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
% 0.35/0.54  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
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
% 0.35/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.35/0.54         (~ (v1_funct_2 @ X61 @ X59 @ X60)
% 0.35/0.54          | ((X59) = (k1_relset_1 @ X59 @ X60 @ X61))
% 0.35/0.54          | ~ (zip_tseitin_1 @ X61 @ X60 @ X59))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      ((~ (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.54  thf(zf_stmt_2, axiom,
% 0.35/0.54    (![B:$i,A:$i]:
% 0.35/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X57 : $i, X58 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X57 @ X58) | ((X57) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_5, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.35/0.54         (~ (zip_tseitin_0 @ X62 @ X63)
% 0.35/0.54          | (zip_tseitin_1 @ X64 @ X62 @ X63)
% 0.35/0.54          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X62))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.54        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.35/0.54        | (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '7'])).
% 0.35/0.54  thf(t20_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.54         ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ( A ) != ( B ) ) ))).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X37 : $i, X38 : $i]:
% 0.35/0.54         (((X38) != (X37))
% 0.35/0.54          | ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X37))
% 0.35/0.54              != (k1_tarski @ X38)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X37 : $i]:
% 0.35/0.54         ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X37))
% 0.35/0.54           != (k1_tarski @ X37))),
% 0.35/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.35/0.54  thf(redefinition_k6_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X43 : $i, X44 : $i]:
% 0.35/0.54         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.54  thf(t92_xboole_1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.54  thf('12', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.35/0.54  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.35/0.54  thf(t100_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X1 : $i, X2 : $i]:
% 0.35/0.54         ((k4_xboole_0 @ X1 @ X2)
% 0.35/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X43 : $i, X44 : $i]:
% 0.35/0.54         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X1 : $i, X2 : $i]:
% 0.35/0.54         ((k6_subset_1 @ X1 @ X2)
% 0.35/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['13', '16'])).
% 0.35/0.54  thf('18', plain, (![X3 : $i]: ((k6_subset_1 @ X3 @ X3) = (k1_xboole_0))),
% 0.35/0.54      inference('demod', [status(thm)], ['12', '17'])).
% 0.35/0.54  thf('19', plain, (![X37 : $i]: ((k1_xboole_0) != (k1_tarski @ X37))),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '11', '18'])).
% 0.35/0.54  thf('20', plain, ((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.35/0.54      inference('clc', [status(thm)], ['8', '19'])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.35/0.54         (((k1_relset_1 @ X55 @ X56 @ X54) = (k1_relat_1 @ X54))
% 0.35/0.54          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56))))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.54  thf('24', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['3', '20', '23'])).
% 0.35/0.54  thf(d4_funct_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.54       ( ![B:$i,C:$i]:
% 0.35/0.54         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.54             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.54               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.35/0.54             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.35/0.54               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i, X50 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X47 @ (k1_relat_1 @ X48))
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X47 @ X50) @ X48)
% 0.35/0.54          | ((X50) != (k1_funct_1 @ X48 @ X47))
% 0.35/0.54          | ~ (v1_funct_1 @ X48)
% 0.35/0.54          | ~ (v1_relat_1 @ X48))),
% 0.35/0.54      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X48)
% 0.35/0.54          | ~ (v1_funct_1 @ X48)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X47 @ (k1_funct_1 @ X48 @ X47)) @ X48)
% 0.35/0.54          | ~ (r2_hidden @ X47 @ (k1_relat_1 @ X48)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D)
% 0.35/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.35/0.54          | ~ (v1_relat_1 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['24', '26'])).
% 0.35/0.54  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( v1_relat_1 @ C ) ))).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.35/0.54         ((v1_relat_1 @ X51)
% 0.35/0.54          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.54  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['27', '28', '31'])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['0', '32'])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(l3_subset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X40 @ X41)
% 0.35/0.54          | (r2_hidden @ X40 @ X42)
% 0.35/0.54          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.35/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.35/0.54          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ 
% 0.35/0.54        (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['33', '36'])).
% 0.35/0.54  thf(t129_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( r2_hidden @
% 0.35/0.54         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.35/0.54       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.54         (((X34) = (X35))
% 0.35/0.54          | ~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ 
% 0.35/0.54               (k2_zfmisc_1 @ X33 @ (k1_tarski @ X35))))),
% 0.35/0.54      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.35/0.54  thf('39', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('40', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('41', plain, ($false),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
