%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jeIDWPiBtW

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:57 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   79 (  99 expanded)
%              Number of leaves         :   38 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  587 (1107 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t6_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k7_relset_1 @ X24 @ X25 @ X26 @ X24 )
        = ( k2_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('3',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
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

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_2 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_1 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_1 @ X32 @ X33 )
      | ( zip_tseitin_2 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ( X6
       != ( k1_funct_1 @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('25',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X8 ) )
      | ( zip_tseitin_0 @ X5 @ ( k1_funct_1 @ X8 @ X5 ) @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_C @ X0 )
      | ( zip_tseitin_0 @ sk_C @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    zip_tseitin_0 @ sk_C @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ sk_A @ sk_D_1 ),
    inference('sup-',[status(thm)],['8','27'])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X13
       != ( k9_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X15 @ X13 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X10 @ X11 )
      | ( r2_hidden @ X15 @ ( k9_relat_1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','7','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jeIDWPiBtW
% 0.15/0.36  % Computer   : n014.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 15:05:52 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 107 iterations in 0.147s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.62  thf(t6_funct_2, conjecture,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.62       ( ( r2_hidden @ C @ A ) =>
% 0.42/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.62          ( ( r2_hidden @ C @ A ) =>
% 0.42/0.62            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62              ( r2_hidden @
% 0.42/0.62                ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t6_funct_2])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (~ (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ 
% 0.42/0.62          (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t38_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.42/0.62         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (((k7_relset_1 @ X24 @ X25 @ X26 @ X24)
% 0.42/0.62            = (k2_relset_1 @ X24 @ X25 @ X26))
% 0.42/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.42/0.62      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_A)
% 0.42/0.62         = (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k7_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.42/0.62          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.42/0.62           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (((k9_relat_1 @ sk_D_1 @ sk_A) = (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['3', '6'])).
% 0.42/0.62  thf('8', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('9', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('10', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d1_funct_2, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_1, axiom,
% 0.42/0.62    (![C:$i,B:$i,A:$i]:
% 0.42/0.62     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.42/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.42/0.62         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.42/0.62          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.42/0.62          | ~ (zip_tseitin_2 @ X31 @ X30 @ X29))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.42/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.62  thf(zf_stmt_2, axiom,
% 0.42/0.62    (![B:$i,A:$i]:
% 0.42/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62       ( zip_tseitin_1 @ B @ A ) ))).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X27 : $i, X28 : $i]:
% 0.42/0.62         ((zip_tseitin_1 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_5, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.42/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.62         (~ (zip_tseitin_1 @ X32 @ X33)
% 0.42/0.62          | (zip_tseitin_2 @ X34 @ X32 @ X33)
% 0.42/0.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.42/0.62        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['13', '16'])).
% 0.42/0.62  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('19', plain, ((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.62         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.42/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('23', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.42/0.62  thf(d12_funct_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i,C:$i]:
% 0.42/0.62         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.42/0.62           ( ![D:$i]:
% 0.42/0.62             ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.62               ( ?[E:$i]:
% 0.42/0.62                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.42/0.62                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_6, axiom,
% 0.42/0.62    (![E:$i,D:$i,B:$i,A:$i]:
% 0.42/0.62     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.42/0.62       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.42/0.62         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.42/0.62          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X8))
% 0.42/0.62          | ~ (r2_hidden @ X5 @ X7)
% 0.42/0.62          | ((X6) != (k1_funct_1 @ X8 @ X5)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X5 @ X7)
% 0.42/0.62          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X8))
% 0.42/0.62          | (zip_tseitin_0 @ X5 @ (k1_funct_1 @ X8 @ X5) @ X7 @ X8))),
% 0.42/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.62          | (zip_tseitin_0 @ X0 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1 @ sk_D_1)
% 0.42/0.62          | ~ (r2_hidden @ X0 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ sk_C @ X0)
% 0.42/0.62          | (zip_tseitin_0 @ sk_C @ (k1_funct_1 @ sk_D_1 @ sk_C) @ X0 @ sk_D_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['9', '26'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      ((zip_tseitin_0 @ sk_C @ (k1_funct_1 @ sk_D_1 @ sk_C) @ sk_A @ sk_D_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '27'])).
% 0.42/0.62  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_8, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i,C:$i]:
% 0.42/0.62         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.42/0.62           ( ![D:$i]:
% 0.42/0.62             ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.62               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.42/0.62         (((X13) != (k9_relat_1 @ X11 @ X10))
% 0.42/0.62          | (r2_hidden @ X15 @ X13)
% 0.42/0.62          | ~ (zip_tseitin_0 @ X16 @ X15 @ X10 @ X11)
% 0.42/0.62          | ~ (v1_funct_1 @ X11)
% 0.42/0.62          | ~ (v1_relat_1 @ X11))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i, X15 : $i, X16 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X11)
% 0.42/0.62          | ~ (v1_funct_1 @ X11)
% 0.42/0.62          | ~ (zip_tseitin_0 @ X16 @ X15 @ X10 @ X11)
% 0.42/0.62          | (r2_hidden @ X15 @ (k9_relat_1 @ X11 @ X10)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ 
% 0.42/0.62         (k9_relat_1 @ sk_D_1 @ sk_A))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_D_1)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_D_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['28', '30'])).
% 0.42/0.62  thf('32', plain, ((v1_funct_1 @ sk_D_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc2_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.62          | (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.62  thf(fc6_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.62  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 0.42/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k9_relat_1 @ sk_D_1 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['31', '32', '37'])).
% 0.42/0.62  thf('39', plain, ($false),
% 0.42/0.62      inference('demod', [status(thm)], ['0', '7', '38'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
