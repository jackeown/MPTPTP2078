%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wyx2JzOfgz

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:04 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   72 (  90 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  493 ( 907 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

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

thf('16',plain,(
    ! [X8: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( X12
       != ( k1_funct_1 @ X8 @ X13 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('17',plain,(
    ! [X8: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X13 ) @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['18','19','24'])).

thf('26',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('29',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wyx2JzOfgz
% 0.16/0.37  % Computer   : n014.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:39:22 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 100 iterations in 0.144s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.63  thf(t7_funct_2, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63       ( ( r2_hidden @ C @ A ) =>
% 0.45/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.63           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.63          ( ( r2_hidden @ C @ A ) =>
% 0.45/0.63            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.63              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.45/0.63  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('2', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d1_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_1, axiom,
% 0.45/0.63    (![C:$i,B:$i,A:$i]:
% 0.45/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.63         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.45/0.63          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.45/0.63          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.45/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.63  thf(zf_stmt_2, axiom,
% 0.45/0.63    (![B:$i,A:$i]:
% 0.45/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X23 : $i, X24 : $i]:
% 0.45/0.63         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.63  thf(zf_stmt_5, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.63         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.45/0.63          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.45/0.63          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.45/0.63        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '8'])).
% 0.45/0.63  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('11', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.45/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.63  thf('15', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.45/0.63      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.45/0.63  thf(d5_funct_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.63               ( ?[D:$i]:
% 0.45/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.45/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X8 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.63         (((X10) != (k2_relat_1 @ X8))
% 0.45/0.63          | (r2_hidden @ X12 @ X10)
% 0.45/0.63          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.45/0.63          | ((X12) != (k1_funct_1 @ X8 @ X13))
% 0.45/0.63          | ~ (v1_funct_1 @ X8)
% 0.45/0.63          | ~ (v1_relat_1 @ X8))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X8 : $i, X13 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X8)
% 0.45/0.63          | ~ (v1_funct_1 @ X8)
% 0.45/0.63          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.45/0.63          | (r2_hidden @ (k1_funct_1 @ X8 @ X13) @ (k2_relat_1 @ X8)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.63          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.45/0.63          | ~ (v1_funct_1 @ sk_D_2)
% 0.45/0.63          | ~ (v1_relat_1 @ sk_D_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['15', '17'])).
% 0.45/0.63  thf('19', plain, ((v1_funct_1 @ sk_D_2)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X3 : $i, X4 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.45/0.63          | (v1_relat_1 @ X3)
% 0.45/0.63          | ~ (v1_relat_1 @ X4))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.63  thf(fc6_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.63  thf('24', plain, ((v1_relat_1 @ sk_D_2)),
% 0.45/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.63          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.63      inference('demod', [status(thm)], ['18', '19', '24'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k2_relat_1 @ sk_D_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '25'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.63         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.45/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2) @ 
% 0.45/0.63        (k1_zfmisc_1 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.63         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.45/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['29', '32'])).
% 0.45/0.63  thf(l3_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.63          | (r2_hidden @ X0 @ X2)
% 0.45/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.45/0.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.63  thf('36', plain, ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ sk_B)),
% 0.45/0.63      inference('sup-', [status(thm)], ['26', '35'])).
% 0.45/0.63  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
