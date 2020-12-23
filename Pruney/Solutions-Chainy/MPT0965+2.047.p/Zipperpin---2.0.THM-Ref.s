%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.btahYiU2G8

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:04 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 159 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  557 (1748 expanded)
%              Number of equality atoms :   30 (  88 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

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

thf('15',plain,(
    ! [X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( X20
       != ( k1_funct_1 @ X16 @ X21 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('16',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('25',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['25','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.btahYiU2G8
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:28:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 114 iterations in 0.209s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(t7_funct_2, conjecture,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.67       ( ( r2_hidden @ C @ A ) =>
% 0.45/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.67           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.67          ( ( r2_hidden @ C @ A ) =>
% 0.45/0.67            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.67              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.45/0.67  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
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
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.67         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.45/0.67          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.45/0.67          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.45/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf(zf_stmt_2, axiom,
% 0.45/0.67    (![B:$i,A:$i]:
% 0.45/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X31 : $i, X32 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
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
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.67         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.45/0.67          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.45/0.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (((zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)
% 0.45/0.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['4', '7'])).
% 0.45/0.67  thf('9', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('10', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B_1 @ sk_A)),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.67         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.45/0.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf('14', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.45/0.67  thf(d5_funct_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.67               ( ?[D:$i]:
% 0.45/0.67                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.45/0.67                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.45/0.67         (((X18) != (k2_relat_1 @ X16))
% 0.45/0.67          | (r2_hidden @ X20 @ X18)
% 0.45/0.67          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.45/0.67          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 0.45/0.67          | ~ (v1_funct_1 @ X16)
% 0.45/0.67          | ~ (v1_relat_1 @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X16 : $i, X21 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X16)
% 0.45/0.67          | ~ (v1_funct_1 @ X16)
% 0.45/0.67          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.45/0.67          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.67          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.45/0.67          | ~ (v1_funct_1 @ sk_D_2)
% 0.45/0.67          | ~ (v1_relat_1 @ sk_D_2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '16'])).
% 0.45/0.67  thf('18', plain, ((v1_funct_1 @ sk_D_2)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(cc2_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.45/0.67          | (v1_relat_1 @ X11)
% 0.45/0.67          | ~ (v1_relat_1 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.67  thf(fc6_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.67  thf('23', plain, ((v1_relat_1 @ sk_D_2)),
% 0.45/0.67      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.67          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.67      inference('demod', [status(thm)], ['17', '18', '23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k2_relat_1 @ sk_D_2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(dt_k2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.67         ((m1_subset_1 @ (k2_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 0.45/0.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) @ 
% 0.45/0.67        (k1_zfmisc_1 @ sk_B_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.67         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.45/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.45/0.67      inference('demod', [status(thm)], ['28', '31'])).
% 0.45/0.67  thf(t5_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.67          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X8 @ X9)
% 0.45/0.67          | ~ (v1_xboole_0 @ X10)
% 0.45/0.67          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k2_relat_1 @ sk_D_2))),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '24'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.45/0.67      inference('demod', [status(thm)], ['28', '31'])).
% 0.45/0.67  thf(t4_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.67       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X5 @ X6)
% 0.45/0.67          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.45/0.67          | (m1_subset_1 @ X5 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.67          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.67  thf('39', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B_1)),
% 0.45/0.67      inference('sup-', [status(thm)], ['35', '38'])).
% 0.45/0.67  thf(t2_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i]:
% 0.45/0.67         ((r2_hidden @ X3 @ X4)
% 0.45/0.67          | (v1_xboole_0 @ X4)
% 0.45/0.67          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.67        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B_1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf('42', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('43', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.45/0.67      inference('clc', [status(thm)], ['41', '42'])).
% 0.45/0.67  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2))),
% 0.45/0.67      inference('demod', [status(thm)], ['34', '43'])).
% 0.45/0.67  thf('45', plain, ($false), inference('sup-', [status(thm)], ['25', '44'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
