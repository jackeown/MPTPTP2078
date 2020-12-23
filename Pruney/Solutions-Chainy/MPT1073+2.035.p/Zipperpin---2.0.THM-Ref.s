%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8y933KkFoO

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  402 (1102 expanded)
%              Number of equality atoms :   16 (  44 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k7_relset_1 @ X20 @ X21 @ X22 @ X20 )
        = ( k2_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k7_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k9_relat_1 @ X16 @ X19 ) ) ) ),
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

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['10','13'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('24',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('25',plain,(
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

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X23: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8y933KkFoO
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 80 iterations in 0.051s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(t190_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.50       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.20/0.50            ( ![E:$i]:
% 0.20/0.50              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.50            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.50          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.20/0.50               ( ![E:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ E @ B ) =>
% 0.20/0.50                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t38_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.50         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.50         (((k7_relset_1 @ X20 @ X21 @ X22 @ X20)
% 0.20/0.50            = (k2_relset_1 @ X20 @ X21 @ X22))
% 0.20/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.50      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((k7_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 @ sk_B_1)
% 0.20/0.50         = (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.50          | ((k7_relset_1 @ X17 @ X18 @ X16 @ X19) = (k9_relat_1 @ X16 @ X19)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k7_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 @ X0)
% 0.20/0.50           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((k9_relat_1 @ sk_D_1 @ sk_B_1) = (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '6'])).
% 0.20/0.50  thf('8', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.50  thf(t143_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.50         ( ?[D:$i]:
% 0.20/0.50           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.50             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.50             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ X8) @ X9)
% 0.20/0.50          | ~ (v1_relat_1 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.50        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_A) @ 
% 0.20/0.50           sk_D_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( v1_relat_1 @ C ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         ((v1_relat_1 @ X13)
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.50  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_A) @ 
% 0.20/0.50        sk_D_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '13'])).
% 0.20/0.50  thf(t8_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.50           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.20/0.50          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.20/0.50          | ~ (v1_funct_1 @ X11)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.50        | ((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('18', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.50  thf('20', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 0.20/0.50          | ~ (v1_relat_1 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.50        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('24', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf(d2_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.50          | (m1_subset_1 @ X3 @ X4)
% 0.20/0.50          | (v1_xboole_0 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.20/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X23 : $i]:
% 0.20/0.50         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X23))
% 0.20/0.50          | ~ (m1_subset_1 @ X23 @ sk_B_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['19', '30'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
