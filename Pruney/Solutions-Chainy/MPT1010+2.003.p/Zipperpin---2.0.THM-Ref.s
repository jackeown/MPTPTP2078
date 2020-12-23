%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eZdZYlu87N

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:13 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 103 expanded)
%              Number of leaves         :   38 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  536 ( 921 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    r2_hidden @ sk_C_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B ) ),
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

thf('2',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ( X50
        = ( k1_relset_1 @ X50 @ X51 @ X52 ) )
      | ~ ( zip_tseitin_2 @ X52 @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('5',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( zip_tseitin_1 @ X53 @ X54 )
      | ( zip_tseitin_2 @ X55 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X48: $i,X49: $i] :
      ( ( zip_tseitin_1 @ X48 @ X49 )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18 != X17 )
      | ( r2_hidden @ X18 @ X19 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X17: $i] :
      ( r2_hidden @ X17 @ ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    zip_tseitin_2 @ sk_D_2 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k1_relset_1 @ X46 @ X47 @ X45 )
        = ( k1_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['3','15','18'])).

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

thf('20',plain,(
    ! [X31: $i,X33: $i,X35: $i,X36: $i] :
      ( ( X33
       != ( k2_relat_1 @ X31 ) )
      | ( r2_hidden @ X35 @ X33 )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X31 ) )
      | ( X35
       != ( k1_funct_1 @ X31 @ X36 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('21',plain,(
    ! [X31: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X31 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X31 @ X36 ) @ ( k2_relat_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf('28',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_3 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v5_relat_1 @ X42 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v5_relat_1 @ X28 @ X29 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_3 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_3 )
    = sk_B ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_3 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eZdZYlu87N
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:08:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.69  % Solved by: fo/fo7.sh
% 0.50/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.69  % done 266 iterations in 0.231s
% 0.50/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.69  % SZS output start Refutation
% 0.50/0.69  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.50/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.50/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.50/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.50/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.69  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.50/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.50/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.69  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.50/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.69  thf(t65_funct_2, conjecture,
% 0.50/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.50/0.69         ( m1_subset_1 @
% 0.50/0.69           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.50/0.69       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.50/0.69            ( m1_subset_1 @
% 0.50/0.69              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.50/0.69          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.50/0.69    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.50/0.69  thf('0', plain, ((r2_hidden @ sk_C_3 @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(d1_funct_2, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.50/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.50/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.50/0.69  thf(zf_stmt_1, axiom,
% 0.50/0.69    (![C:$i,B:$i,A:$i]:
% 0.50/0.69     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.50/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.50/0.69  thf('2', plain,
% 0.50/0.69      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.50/0.69         (~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.50/0.69          | ((X50) = (k1_relset_1 @ X50 @ X51 @ X52))
% 0.50/0.69          | ~ (zip_tseitin_2 @ X52 @ X51 @ X50))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.69  thf('3', plain,
% 0.50/0.69      ((~ (zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.50/0.69        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.69  thf('4', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D_2 @ 
% 0.50/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.50/0.69  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.50/0.69  thf(zf_stmt_4, axiom,
% 0.50/0.69    (![B:$i,A:$i]:
% 0.50/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.69       ( zip_tseitin_1 @ B @ A ) ))).
% 0.50/0.69  thf(zf_stmt_5, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.50/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.50/0.69  thf('5', plain,
% 0.50/0.69      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.50/0.69         (~ (zip_tseitin_1 @ X53 @ X54)
% 0.50/0.69          | (zip_tseitin_2 @ X55 @ X53 @ X54)
% 0.50/0.69          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.69  thf('6', plain,
% 0.50/0.69      (((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)
% 0.50/0.69        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.69  thf('7', plain,
% 0.50/0.69      (![X48 : $i, X49 : $i]:
% 0.50/0.69         ((zip_tseitin_1 @ X48 @ X49) | ((X48) = (k1_xboole_0)))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.50/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.69  thf('8', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.50/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.69  thf('9', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.50/0.69      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.69  thf(d1_tarski, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.50/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.50/0.69  thf('10', plain,
% 0.50/0.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.69         (((X18) != (X17))
% 0.50/0.69          | (r2_hidden @ X18 @ X19)
% 0.50/0.69          | ((X19) != (k1_tarski @ X17)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.50/0.69  thf('11', plain, (![X17 : $i]: (r2_hidden @ X17 @ (k1_tarski @ X17))),
% 0.50/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.50/0.69  thf(t7_ordinal1, axiom,
% 0.50/0.69    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.69  thf('12', plain,
% 0.50/0.69      (![X37 : $i, X38 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X37 @ X38) | ~ (r1_tarski @ X38 @ X37))),
% 0.50/0.69      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.50/0.69  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.50/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.69  thf('14', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.50/0.69      inference('sup-', [status(thm)], ['9', '13'])).
% 0.50/0.69  thf('15', plain, ((zip_tseitin_2 @ sk_D_2 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.50/0.69      inference('demod', [status(thm)], ['6', '14'])).
% 0.50/0.69  thf('16', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D_2 @ 
% 0.50/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.50/0.69  thf('17', plain,
% 0.50/0.69      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.50/0.69         (((k1_relset_1 @ X46 @ X47 @ X45) = (k1_relat_1 @ X45))
% 0.50/0.69          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.50/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.69  thf('18', plain,
% 0.50/0.69      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_2)
% 0.50/0.69         = (k1_relat_1 @ sk_D_2))),
% 0.50/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.50/0.69  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.50/0.69      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.50/0.69  thf(d5_funct_1, axiom,
% 0.50/0.69    (![A:$i]:
% 0.50/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.69       ( ![B:$i]:
% 0.50/0.69         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.50/0.69           ( ![C:$i]:
% 0.50/0.69             ( ( r2_hidden @ C @ B ) <=>
% 0.50/0.69               ( ?[D:$i]:
% 0.50/0.69                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.50/0.69                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.50/0.69  thf('20', plain,
% 0.50/0.69      (![X31 : $i, X33 : $i, X35 : $i, X36 : $i]:
% 0.50/0.69         (((X33) != (k2_relat_1 @ X31))
% 0.50/0.69          | (r2_hidden @ X35 @ X33)
% 0.50/0.69          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ X31))
% 0.50/0.69          | ((X35) != (k1_funct_1 @ X31 @ X36))
% 0.50/0.69          | ~ (v1_funct_1 @ X31)
% 0.50/0.69          | ~ (v1_relat_1 @ X31))),
% 0.50/0.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.50/0.69  thf('21', plain,
% 0.50/0.69      (![X31 : $i, X36 : $i]:
% 0.50/0.69         (~ (v1_relat_1 @ X31)
% 0.50/0.69          | ~ (v1_funct_1 @ X31)
% 0.50/0.69          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ X31))
% 0.50/0.69          | (r2_hidden @ (k1_funct_1 @ X31 @ X36) @ (k2_relat_1 @ X31)))),
% 0.50/0.69      inference('simplify', [status(thm)], ['20'])).
% 0.50/0.69  thf('22', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.69          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.50/0.69          | ~ (v1_funct_1 @ sk_D_2)
% 0.50/0.69          | ~ (v1_relat_1 @ sk_D_2))),
% 0.50/0.69      inference('sup-', [status(thm)], ['19', '21'])).
% 0.50/0.69  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('24', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D_2 @ 
% 0.50/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(cc1_relset_1, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( v1_relat_1 @ C ) ))).
% 0.50/0.69  thf('25', plain,
% 0.50/0.69      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.50/0.69         ((v1_relat_1 @ X39)
% 0.50/0.69          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.50/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.69  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 0.50/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.69  thf('27', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ sk_A)
% 0.50/0.69          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.50/0.69      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.50/0.69  thf('28', plain,
% 0.50/0.69      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_3) @ (k2_relat_1 @ sk_D_2))),
% 0.50/0.69      inference('sup-', [status(thm)], ['0', '27'])).
% 0.50/0.69  thf('29', plain,
% 0.50/0.69      ((m1_subset_1 @ sk_D_2 @ 
% 0.50/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(cc2_relset_1, axiom,
% 0.50/0.69    (![A:$i,B:$i,C:$i]:
% 0.50/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.50/0.69  thf('30', plain,
% 0.50/0.69      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.50/0.69         ((v5_relat_1 @ X42 @ X44)
% 0.50/0.69          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.50/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.69  thf('31', plain, ((v5_relat_1 @ sk_D_2 @ (k1_tarski @ sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.69  thf(d19_relat_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( v1_relat_1 @ B ) =>
% 0.50/0.69       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.50/0.69  thf('32', plain,
% 0.50/0.69      (![X28 : $i, X29 : $i]:
% 0.50/0.69         (~ (v5_relat_1 @ X28 @ X29)
% 0.50/0.69          | (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.50/0.69          | ~ (v1_relat_1 @ X28))),
% 0.50/0.69      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.50/0.69  thf('33', plain,
% 0.50/0.69      ((~ (v1_relat_1 @ sk_D_2)
% 0.50/0.69        | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.69  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.50/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.69  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B))),
% 0.50/0.69      inference('demod', [status(thm)], ['33', '34'])).
% 0.50/0.69  thf(d3_tarski, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.69  thf('36', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.69          | (r2_hidden @ X0 @ X2)
% 0.50/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.69  thf('37', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.50/0.69          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.50/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.50/0.69  thf('38', plain,
% 0.50/0.69      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_3) @ (k1_tarski @ sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['28', '37'])).
% 0.50/0.69  thf('39', plain,
% 0.50/0.69      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.50/0.69         (~ (r2_hidden @ X20 @ X19)
% 0.50/0.69          | ((X20) = (X17))
% 0.50/0.69          | ((X19) != (k1_tarski @ X17)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.50/0.69  thf('40', plain,
% 0.50/0.69      (![X17 : $i, X20 : $i]:
% 0.50/0.69         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.50/0.69      inference('simplify', [status(thm)], ['39'])).
% 0.50/0.69  thf('41', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_3) = (sk_B))),
% 0.50/0.69      inference('sup-', [status(thm)], ['38', '40'])).
% 0.50/0.69  thf('42', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_3) != (sk_B))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('43', plain, ($false),
% 0.50/0.69      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
