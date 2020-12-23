%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h2QeehQdGU

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 106 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  440 (1191 expanded)
%              Number of equality atoms :   21 (  52 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k7_relset_1 @ X29 @ X30 @ X31 @ X29 )
        = ( k2_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('3',plain,
    ( ( k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ),
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
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X18
       != ( k9_relat_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_A @ sk_B @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_A @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X11
        = ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_A @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12','15'])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ X12 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X32: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h2QeehQdGU
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 60 iterations in 0.052s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(t190_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.51       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.21/0.51            ( ![E:$i]:
% 0.21/0.51              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.51            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.51          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.21/0.51               ( ![E:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ E @ B ) =>
% 0.21/0.51                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.21/0.51  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t38_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.51         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.51         (((k7_relset_1 @ X29 @ X30 @ X31 @ X29)
% 0.21/0.51            = (k2_relset_1 @ X29 @ X30 @ X31))
% 0.21/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ sk_B)
% 0.21/0.51         = (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.21/0.51          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.21/0.51           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((k9_relat_1 @ sk_D_1 @ sk_B) = (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.51  thf('8', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.51  thf(d12_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.51       ( ![B:$i,C:$i]:
% 0.21/0.51         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.21/0.51           ( ![D:$i]:
% 0.21/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51               ( ?[E:$i]:
% 0.21/0.51                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.51                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_2, axiom,
% 0.21/0.51    (![E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.21/0.51       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.21/0.51         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( ![B:$i,C:$i]:
% 0.21/0.51         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.21/0.51           ( ![D:$i]:
% 0.21/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         (((X18) != (k9_relat_1 @ X16 @ X15))
% 0.21/0.51          | (zip_tseitin_0 @ (sk_E_1 @ X19 @ X15 @ X16) @ X19 @ X15 @ X16)
% 0.21/0.51          | ~ (r2_hidden @ X19 @ X18)
% 0.21/0.51          | ~ (v1_funct_1 @ X16)
% 0.21/0.51          | ~ (v1_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X19 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X16)
% 0.21/0.51          | ~ (v1_funct_1 @ X16)
% 0.21/0.51          | ~ (r2_hidden @ X19 @ (k9_relat_1 @ X16 @ X15))
% 0.21/0.51          | (zip_tseitin_0 @ (sk_E_1 @ X19 @ X15 @ X16) @ X19 @ X15 @ X16))),
% 0.21/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_A @ sk_B @ sk_D_1)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.51  thf('12', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_A @ sk_B @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         (((X11) = (k1_funct_1 @ X9 @ X10))
% 0.21/0.51          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_A @ sk_B @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12', '15'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         ((r2_hidden @ X10 @ X12) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.51  thf('21', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X3 : $i, X5 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('25', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf(t4_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.51          | (m1_subset_1 @ X6 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain, ((m1_subset_1 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X32 : $i]:
% 0.21/0.51         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X32))
% 0.21/0.51          | ~ (m1_subset_1 @ X32 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['18', '30'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
