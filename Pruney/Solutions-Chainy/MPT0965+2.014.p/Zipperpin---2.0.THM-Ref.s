%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rYX20Cj3fh

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   73 (  91 expanded)
%              Number of leaves         :   34 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  495 ( 909 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('27',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rYX20Cj3fh
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 102 iterations in 0.108s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(t7_funct_2, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.55       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.55            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.55          ( ( r2_hidden @ C @ A ) =>
% 0.21/0.55            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.21/0.55  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('2', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d1_funct_2, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_1, axiom,
% 0.21/0.55    (![C:$i,B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.55         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.21/0.55          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.21/0.55          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.21/0.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf(zf_stmt_2, axiom,
% 0.21/0.55    (![B:$i,A:$i]:
% 0.21/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_5, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.55         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.21/0.55          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.21/0.55          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.21/0.55        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.55  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('11', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.40/0.55      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.55    (![A:$i,B:$i,C:$i]:
% 0.40/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.55  thf('13', plain,
% 0.40/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.55         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.40/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.40/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.55  thf('14', plain,
% 0.40/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.40/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.55  thf('15', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.40/0.55      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.40/0.55  thf(d5_funct_1, axiom,
% 0.40/0.55    (![A:$i]:
% 0.40/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.55       ( ![B:$i]:
% 0.40/0.55         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.40/0.55           ( ![C:$i]:
% 0.40/0.55             ( ( r2_hidden @ C @ B ) <=>
% 0.40/0.55               ( ?[D:$i]:
% 0.40/0.55                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.40/0.55                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.40/0.55  thf('16', plain,
% 0.40/0.55      (![X8 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.55         (((X10) != (k2_relat_1 @ X8))
% 0.40/0.55          | (r2_hidden @ X12 @ X10)
% 0.40/0.55          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.40/0.55          | ((X12) != (k1_funct_1 @ X8 @ X13))
% 0.40/0.55          | ~ (v1_funct_1 @ X8)
% 0.40/0.55          | ~ (v1_relat_1 @ X8))),
% 0.40/0.55      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.40/0.55  thf('17', plain,
% 0.40/0.55      (![X8 : $i, X13 : $i]:
% 0.40/0.55         (~ (v1_relat_1 @ X8)
% 0.40/0.55          | ~ (v1_funct_1 @ X8)
% 0.40/0.55          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.40/0.55          | (r2_hidden @ (k1_funct_1 @ X8 @ X13) @ (k2_relat_1 @ X8)))),
% 0.40/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.55  thf('18', plain,
% 0.40/0.55      (![X0 : $i]:
% 0.40/0.55         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.55          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.40/0.55          | ~ (v1_funct_1 @ sk_D_2)
% 0.40/0.55          | ~ (v1_relat_1 @ sk_D_2))),
% 0.40/0.55      inference('sup-', [status(thm)], ['15', '17'])).
% 0.40/0.55  thf('19', plain, ((v1_funct_1 @ sk_D_2)),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf('20', plain,
% 0.40/0.55      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf(cc1_relset_1, axiom,
% 0.40/0.55    (![A:$i,B:$i,C:$i]:
% 0.40/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.55       ( v1_relat_1 @ C ) ))).
% 0.40/0.55  thf('21', plain,
% 0.40/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.55         ((v1_relat_1 @ X14)
% 0.40/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.40/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.55  thf('22', plain, ((v1_relat_1 @ sk_D_2)),
% 0.40/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.55  thf('23', plain,
% 0.40/0.55      (![X0 : $i]:
% 0.40/0.55         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.55          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.40/0.55      inference('demod', [status(thm)], ['18', '19', '22'])).
% 0.40/0.55  thf('24', plain,
% 0.40/0.55      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))),
% 0.40/0.55      inference('sup-', [status(thm)], ['1', '23'])).
% 0.40/0.55  thf('25', plain,
% 0.40/0.55      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf(dt_k2_relset_1, axiom,
% 0.40/0.55    (![A:$i,B:$i,C:$i]:
% 0.40/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.55       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.40/0.55  thf('26', plain,
% 0.40/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.55         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.40/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.40/0.55      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.40/0.55  thf('27', plain,
% 0.40/0.55      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2) @ 
% 0.40/0.55        (k1_zfmisc_1 @ sk_B))),
% 0.40/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.55  thf('28', plain,
% 0.40/0.55      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.55    (![A:$i,B:$i,C:$i]:
% 0.40/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.55  thf('29', plain,
% 0.40/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.55         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.40/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.40/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.55  thf('30', plain,
% 0.40/0.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.40/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.55  thf('31', plain,
% 0.40/0.55      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.40/0.55      inference('demod', [status(thm)], ['27', '30'])).
% 0.40/0.55  thf(t3_subset, axiom,
% 0.40/0.55    (![A:$i,B:$i]:
% 0.40/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.55  thf('32', plain,
% 0.40/0.55      (![X4 : $i, X5 : $i]:
% 0.40/0.55         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.40/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.55  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B)),
% 0.40/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.55  thf(d3_tarski, axiom,
% 0.40/0.55    (![A:$i,B:$i]:
% 0.40/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.55  thf('34', plain,
% 0.40/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.55          | (r2_hidden @ X0 @ X2)
% 0.40/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.55  thf('35', plain,
% 0.40/0.55      (![X0 : $i]:
% 0.40/0.55         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.40/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.55  thf('36', plain, ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ sk_B)),
% 0.40/0.55      inference('sup-', [status(thm)], ['24', '35'])).
% 0.40/0.55  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.40/0.55  
% 0.40/0.55  % SZS output end Refutation
% 0.40/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
