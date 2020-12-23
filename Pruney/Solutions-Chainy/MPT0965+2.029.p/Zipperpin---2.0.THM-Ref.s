%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0CjOlv9fGk

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:01 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 112 expanded)
%              Number of leaves         :   41 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  534 ( 984 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v5_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ),
    inference(demod,[status(thm)],['5','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r2_hidden @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
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

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['21','28','31'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X21 @ X20 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('36',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k3_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k2_relat_1 @ sk_D_2 ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','41'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('43',plain,(
    ! [X7: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('44',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0CjOlv9fGk
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 139 iterations in 0.200s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.47/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.47/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(t7_funct_2, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.66       ( ( r2_hidden @ C @ A ) =>
% 0.47/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.66           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.66            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.66          ( ( r2_hidden @ C @ A ) =>
% 0.47/0.66            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.66              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.47/0.66  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc2_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.66         ((v5_relat_1 @ X22 @ X24)
% 0.47/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.66  thf('3', plain, ((v5_relat_1 @ sk_D_2 @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf(d19_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (![X16 : $i, X17 : $i]:
% 0.47/0.66         (~ (v5_relat_1 @ X16 @ X17)
% 0.47/0.66          | (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.47/0.66          | ~ (v1_relat_1 @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(cc2_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.47/0.66          | (v1_relat_1 @ X14)
% 0.47/0.66          | ~ (v1_relat_1 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.66  thf(fc6_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.66  thf('10', plain, ((v1_relat_1 @ sk_D_2)),
% 0.47/0.66      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B)),
% 0.47/0.66      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.66  thf(t3_subset, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X11 : $i, X13 : $i]:
% 0.47/0.66         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.66  thf(t2_subset, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ A @ B ) =>
% 0.47/0.66       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X9 : $i, X10 : $i]:
% 0.47/0.66         ((r2_hidden @ X9 @ X10)
% 0.47/0.66          | (v1_xboole_0 @ X10)
% 0.47/0.66          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_subset])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.47/0.66        | (r2_hidden @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf(fc1_subset_1, axiom,
% 0.47/0.66    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.66  thf('16', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      ((r2_hidden @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.47/0.66      inference('clc', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('19', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d1_funct_2, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_1, axiom,
% 0.47/0.66    (![C:$i,B:$i,A:$i]:
% 0.47/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.47/0.66         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.47/0.66          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.47/0.66          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.47/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.66  thf(zf_stmt_2, axiom,
% 0.47/0.66    (![B:$i,A:$i]:
% 0.47/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.66       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X28 : $i, X29 : $i]:
% 0.47/0.66         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.66  thf(zf_stmt_5, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.66         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.47/0.66          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.47/0.66          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.47/0.66        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '25'])).
% 0.47/0.66  thf('27', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('28', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.66         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.47/0.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.66  thf('32', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.47/0.66      inference('demod', [status(thm)], ['21', '28', '31'])).
% 0.47/0.66  thf(t12_funct_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.66       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.66         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X20 : $i, X21 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.47/0.66          | (r2_hidden @ (k1_funct_1 @ X21 @ X20) @ (k2_relat_1 @ X21))
% 0.47/0.66          | ~ (v1_funct_1 @ X21)
% 0.47/0.66          | ~ (v1_relat_1 @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ sk_A)
% 0.47/0.66          | ~ (v1_relat_1 @ sk_D_2)
% 0.47/0.66          | ~ (v1_funct_1 @ sk_D_2)
% 0.47/0.66          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain, ((v1_relat_1 @ sk_D_2)),
% 0.47/0.66      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('36', plain, ((v1_funct_1 @ sk_D_2)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ sk_A)
% 0.47/0.66          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.47/0.66      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k2_relat_1 @ sk_D_2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['18', '37'])).
% 0.47/0.66  thf(d4_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.47/0.66       ( ![C:$i]:
% 0.47/0.66         ( ( r2_hidden @ C @ B ) <=>
% 0.47/0.66           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | ~ (r2_hidden @ X2 @ X0)
% 0.47/0.66          | (r2_hidden @ X2 @ X3)
% 0.47/0.66          | ((X3) != (k3_tarski @ X1)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_tarski])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r2_hidden @ X2 @ (k3_tarski @ X1))
% 0.47/0.66          | ~ (r2_hidden @ X2 @ X0)
% 0.47/0.66          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_hidden @ (k2_relat_1 @ sk_D_2) @ X0)
% 0.47/0.66          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k3_tarski @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['38', '40'])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ 
% 0.47/0.66        (k3_tarski @ (k1_zfmisc_1 @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['17', '41'])).
% 0.47/0.66  thf(t99_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.47/0.66  thf('43', plain, (![X7 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X7)) = (X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.47/0.66  thf('44', plain, ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B)),
% 0.47/0.66      inference('demod', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
