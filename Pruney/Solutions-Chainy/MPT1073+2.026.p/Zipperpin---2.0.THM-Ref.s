%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WInMxxY0xH

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:17 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 103 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  420 (1171 expanded)
%              Number of equality atoms :   20 (  51 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k7_relset_1 @ X26 @ X27 @ X28 @ X26 )
        = ( k2_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('3',plain,
    ( ( k7_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 @ sk_B_1 )
    = ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_B_1 )
    = ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','7'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
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

thf('9',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k9_relat_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X16 @ X12 @ X13 ) @ X16 @ X12 @ X13 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X16 @ X12 @ X13 ) @ X16 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1 ) @ sk_A @ sk_B_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1 ) @ sk_A @ sk_B_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X9 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X29: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1 ) @ sk_A @ sk_B_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8
        = ( k1_funct_1 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WInMxxY0xH
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 123 iterations in 0.161s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.43/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.61  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.43/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.43/0.61  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.43/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(t190_funct_2, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.43/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.43/0.61       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.43/0.61            ( ![E:$i]:
% 0.43/0.61              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.43/0.61            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.43/0.61          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.43/0.61               ( ![E:$i]:
% 0.43/0.61                 ( ( m1_subset_1 @ E @ B ) =>
% 0.43/0.61                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t38_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.43/0.61         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.43/0.61         (((k7_relset_1 @ X26 @ X27 @ X28 @ X26)
% 0.43/0.61            = (k2_relset_1 @ X26 @ X27 @ X28))
% 0.43/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.43/0.61      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (((k7_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 @ sk_B_1)
% 0.43/0.61         = (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(redefinition_k7_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.43/0.61          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k7_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 @ X0)
% 0.43/0.61           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (((k9_relat_1 @ sk_D_1 @ sk_B_1) = (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.43/0.61      inference('demod', [status(thm)], ['3', '6'])).
% 0.43/0.61  thf('8', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B_1))),
% 0.43/0.61      inference('demod', [status(thm)], ['0', '7'])).
% 0.43/0.61  thf(d12_funct_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.43/0.61       ( ![B:$i,C:$i]:
% 0.43/0.61         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.43/0.61           ( ![D:$i]:
% 0.43/0.61             ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.61               ( ?[E:$i]:
% 0.43/0.61                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.43/0.61                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.43/0.61  thf(zf_stmt_2, axiom,
% 0.43/0.61    (![E:$i,D:$i,B:$i,A:$i]:
% 0.43/0.61     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.43/0.61       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.43/0.61         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.61       ( ![B:$i,C:$i]:
% 0.43/0.61         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.43/0.61           ( ![D:$i]:
% 0.43/0.61             ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.61               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.43/0.61         (((X15) != (k9_relat_1 @ X13 @ X12))
% 0.43/0.61          | (zip_tseitin_0 @ (sk_E_1 @ X16 @ X12 @ X13) @ X16 @ X12 @ X13)
% 0.43/0.61          | ~ (r2_hidden @ X16 @ X15)
% 0.43/0.61          | ~ (v1_funct_1 @ X13)
% 0.43/0.61          | ~ (v1_relat_1 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X13)
% 0.43/0.61          | ~ (v1_funct_1 @ X13)
% 0.43/0.61          | ~ (r2_hidden @ X16 @ (k9_relat_1 @ X13 @ X12))
% 0.43/0.61          | (zip_tseitin_0 @ (sk_E_1 @ X16 @ X12 @ X13) @ X16 @ X12 @ X13))),
% 0.43/0.61      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1) @ sk_A @ sk_B_1 @ 
% 0.43/0.61         sk_D_1)
% 0.43/0.61        | ~ (v1_funct_1 @ sk_D_1)
% 0.43/0.61        | ~ (v1_relat_1 @ sk_D_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['8', '10'])).
% 0.43/0.61  thf('12', plain, ((v1_funct_1 @ sk_D_1)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc1_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( v1_relat_1 @ C ) ))).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.61         ((v1_relat_1 @ X19)
% 0.43/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.43/0.61  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.43/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      ((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1) @ sk_A @ sk_B_1 @ 
% 0.43/0.61        sk_D_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.61         ((r2_hidden @ X7 @ X9) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.61  thf('18', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1) @ sk_B_1)),
% 0.43/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.61  thf(d2_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.43/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.43/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X3 @ X4)
% 0.43/0.61          | (m1_subset_1 @ X3 @ X4)
% 0.43/0.61          | (v1_xboole_0 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.61  thf(d1_xboole_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.43/0.61      inference('clc', [status(thm)], ['19', '20'])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      ((m1_subset_1 @ (sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1) @ sk_B_1)),
% 0.43/0.61      inference('sup-', [status(thm)], ['18', '21'])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X29 : $i]:
% 0.43/0.61         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X29))
% 0.43/0.61          | ~ (m1_subset_1 @ X29 @ sk_B_1))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      ((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1) @ sk_A @ sk_B_1 @ 
% 0.43/0.61        sk_D_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.61         (((X8) = (k1_funct_1 @ X6 @ X7))
% 0.43/0.61          | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.61  thf('28', plain, (((sk_A) != (sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['24', '27'])).
% 0.43/0.61  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
