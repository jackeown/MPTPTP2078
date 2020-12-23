%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O9NWSeeu9Q

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:27 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   84 (  99 expanded)
%              Number of leaves         :   39 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  532 ( 850 expanded)
%              Number of equality atoms :   35 (  51 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X26 @ X25 ) @ X27 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v5_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D_1 @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['2','33'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O9NWSeeu9Q
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:42:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.48  % Solved by: fo/fo7.sh
% 0.18/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.48  % done 96 iterations in 0.041s
% 0.18/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.48  % SZS output start Refutation
% 0.18/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.18/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.18/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.18/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.18/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.18/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.18/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.18/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.18/0.48  thf(t65_funct_2, conjecture,
% 0.18/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.18/0.48         ( m1_subset_1 @
% 0.18/0.48           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.18/0.48       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.18/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.48        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.18/0.48            ( m1_subset_1 @
% 0.18/0.48              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.18/0.48          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.18/0.48    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.18/0.48  thf('0', plain,
% 0.18/0.48      ((m1_subset_1 @ sk_D_1 @ 
% 0.18/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf(cc2_relset_1, axiom,
% 0.18/0.48    (![A:$i,B:$i,C:$i]:
% 0.18/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.18/0.48  thf('1', plain,
% 0.18/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.18/0.48         ((v5_relat_1 @ X30 @ X32)
% 0.18/0.48          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.18/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.18/0.48  thf('2', plain, ((v5_relat_1 @ sk_D_1 @ (k1_tarski @ sk_B))),
% 0.18/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.48  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf(d1_funct_2, axiom,
% 0.18/0.48    (![A:$i,B:$i,C:$i]:
% 0.18/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.18/0.48           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.18/0.48             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.18/0.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.18/0.48           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.18/0.48             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.18/0.48  thf(zf_stmt_1, axiom,
% 0.18/0.48    (![B:$i,A:$i]:
% 0.18/0.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.18/0.48       ( zip_tseitin_0 @ B @ A ) ))).
% 0.18/0.48  thf('4', plain,
% 0.18/0.48      (![X36 : $i, X37 : $i]:
% 0.18/0.48         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.18/0.48  thf('5', plain,
% 0.18/0.48      ((m1_subset_1 @ sk_D_1 @ 
% 0.18/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.18/0.48  thf(zf_stmt_3, axiom,
% 0.18/0.48    (![C:$i,B:$i,A:$i]:
% 0.18/0.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.18/0.48       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.18/0.48  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.18/0.48  thf(zf_stmt_5, axiom,
% 0.18/0.48    (![A:$i,B:$i,C:$i]:
% 0.18/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.48       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.18/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.18/0.48           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.18/0.48             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.18/0.48  thf('6', plain,
% 0.18/0.48      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.18/0.48         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.18/0.48          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.18/0.48          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.18/0.48  thf('7', plain,
% 0.18/0.48      (((zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B) @ sk_A)
% 0.18/0.48        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.18/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.48  thf('8', plain,
% 0.18/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.18/0.48        | (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.18/0.48      inference('sup-', [status(thm)], ['4', '7'])).
% 0.18/0.48  thf('9', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf('10', plain,
% 0.18/0.48      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.18/0.48         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.18/0.48          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.18/0.48          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.18/0.48  thf('11', plain,
% 0.18/0.48      ((~ (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B) @ sk_A)
% 0.18/0.48        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_1)))),
% 0.18/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.48  thf('12', plain,
% 0.18/0.48      ((m1_subset_1 @ sk_D_1 @ 
% 0.18/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.18/0.48    (![A:$i,B:$i,C:$i]:
% 0.18/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.18/0.48  thf('13', plain,
% 0.18/0.48      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.18/0.48         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.18/0.48          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.18/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.18/0.48  thf('14', plain,
% 0.18/0.48      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_1)
% 0.18/0.48         = (k1_relat_1 @ sk_D_1))),
% 0.18/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.48  thf('15', plain,
% 0.18/0.48      ((~ (zip_tseitin_1 @ sk_D_1 @ (k1_tarski @ sk_B) @ sk_A)
% 0.18/0.48        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.18/0.48      inference('demod', [status(thm)], ['11', '14'])).
% 0.18/0.48  thf('16', plain,
% 0.18/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.18/0.48      inference('sup-', [status(thm)], ['8', '15'])).
% 0.18/0.48  thf(d1_tarski, axiom,
% 0.18/0.48    (![A:$i,B:$i]:
% 0.18/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.18/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.18/0.48  thf('17', plain,
% 0.18/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.18/0.48         (((X2) != (X1)) | (r2_hidden @ X2 @ X3) | ((X3) != (k1_tarski @ X1)))),
% 0.18/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.18/0.48  thf('18', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.18/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.18/0.48  thf(t7_ordinal1, axiom,
% 0.18/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.48  thf('19', plain,
% 0.18/0.48      (![X28 : $i, X29 : $i]:
% 0.18/0.48         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 0.18/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.18/0.48  thf('20', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.18/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.48  thf('21', plain,
% 0.18/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.18/0.48      inference('sup-', [status(thm)], ['16', '20'])).
% 0.18/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.48  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.18/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.48  thf('23', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.18/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.18/0.48  thf(t176_funct_1, axiom,
% 0.18/0.48    (![A:$i,B:$i,C:$i]:
% 0.18/0.48     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.18/0.48       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.18/0.48         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.18/0.48  thf('24', plain,
% 0.18/0.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.18/0.48         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.18/0.48          | (m1_subset_1 @ (k1_funct_1 @ X26 @ X25) @ X27)
% 0.18/0.48          | ~ (v1_funct_1 @ X26)
% 0.18/0.48          | ~ (v5_relat_1 @ X26 @ X27)
% 0.18/0.48          | ~ (v1_relat_1 @ X26))),
% 0.18/0.48      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.18/0.48  thf('25', plain,
% 0.18/0.48      (![X0 : $i, X1 : $i]:
% 0.18/0.48         (~ (r2_hidden @ X0 @ sk_A)
% 0.18/0.48          | ~ (v1_relat_1 @ sk_D_1)
% 0.18/0.48          | ~ (v5_relat_1 @ sk_D_1 @ X1)
% 0.18/0.48          | ~ (v1_funct_1 @ sk_D_1)
% 0.18/0.48          | (m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1))),
% 0.18/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.18/0.48  thf('26', plain,
% 0.18/0.48      ((m1_subset_1 @ sk_D_1 @ 
% 0.18/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf(cc2_relat_1, axiom,
% 0.18/0.48    (![A:$i]:
% 0.18/0.48     ( ( v1_relat_1 @ A ) =>
% 0.18/0.48       ( ![B:$i]:
% 0.18/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.18/0.48  thf('27', plain,
% 0.18/0.48      (![X21 : $i, X22 : $i]:
% 0.18/0.48         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.18/0.48          | (v1_relat_1 @ X21)
% 0.18/0.48          | ~ (v1_relat_1 @ X22))),
% 0.18/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.18/0.48  thf('28', plain,
% 0.18/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.18/0.48        | (v1_relat_1 @ sk_D_1))),
% 0.18/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.18/0.48  thf(fc6_relat_1, axiom,
% 0.18/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.18/0.48  thf('29', plain,
% 0.18/0.48      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.18/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.18/0.48  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.18/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.18/0.48  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf('32', plain,
% 0.18/0.48      (![X0 : $i, X1 : $i]:
% 0.18/0.48         (~ (r2_hidden @ X0 @ sk_A)
% 0.18/0.48          | ~ (v5_relat_1 @ sk_D_1 @ X1)
% 0.18/0.48          | (m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1))),
% 0.18/0.48      inference('demod', [status(thm)], ['25', '30', '31'])).
% 0.18/0.48  thf('33', plain,
% 0.18/0.48      (![X0 : $i]:
% 0.18/0.48         ((m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ X0)
% 0.18/0.48          | ~ (v5_relat_1 @ sk_D_1 @ X0))),
% 0.18/0.48      inference('sup-', [status(thm)], ['3', '32'])).
% 0.18/0.48  thf('34', plain,
% 0.18/0.48      ((m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.18/0.48      inference('sup-', [status(thm)], ['2', '33'])).
% 0.18/0.48  thf(t2_subset, axiom,
% 0.18/0.48    (![A:$i,B:$i]:
% 0.18/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.18/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.18/0.48  thf('35', plain,
% 0.18/0.48      (![X19 : $i, X20 : $i]:
% 0.18/0.48         ((r2_hidden @ X19 @ X20)
% 0.18/0.48          | (v1_xboole_0 @ X20)
% 0.18/0.48          | ~ (m1_subset_1 @ X19 @ X20))),
% 0.18/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.18/0.48  thf('36', plain,
% 0.18/0.48      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.18/0.48        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.18/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.48  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.18/0.48  thf('37', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X18))),
% 0.18/0.48      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.18/0.48  thf('38', plain,
% 0.18/0.48      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.18/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.18/0.48  thf('39', plain,
% 0.18/0.48      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.18/0.48         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.18/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.18/0.48  thf('40', plain,
% 0.18/0.48      (![X1 : $i, X4 : $i]:
% 0.18/0.48         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.18/0.48      inference('simplify', [status(thm)], ['39'])).
% 0.18/0.48  thf('41', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B))),
% 0.18/0.48      inference('sup-', [status(thm)], ['38', '40'])).
% 0.18/0.48  thf('42', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B))),
% 0.18/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.48  thf('43', plain, ($false),
% 0.18/0.48      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.18/0.48  
% 0.18/0.48  % SZS output end Refutation
% 0.18/0.48  
% 0.18/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
