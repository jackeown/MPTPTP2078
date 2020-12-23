%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.loi7vRZy57

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:20 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 282 expanded)
%              Number of leaves         :   25 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  425 (3515 expanded)
%              Number of equality atoms :   39 ( 223 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('0',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k6_partfun1 @ X9 )
      = ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t174_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
      <=> ( ( k5_partfun1 @ A @ B @ C )
          = ( k1_tarski @ C ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X13 @ X14 )
      | ( ( k5_partfun1 @ X14 @ X15 @ X13 )
        = ( k1_tarski @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) )
    | ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t162_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) )
        = ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) )
          = ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_2])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X6 ) ) )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t161_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
          = ( k1_tarski @ C ) ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( ( k5_partfun1 @ X10 @ X12 @ ( k3_partfun1 @ X11 @ X10 @ X12 ) )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t161_funct_2])).

thf('13',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k3_partfun1 @ C @ A @ B )
        = C ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k3_partfun1 @ X16 @ X17 @ X18 )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t87_partfun1])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k3_partfun1 @ sk_B @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k3_partfun1 @ sk_B @ sk_A @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','18','19','20'])).

thf('22',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k3_partfun1 @ sk_B @ sk_A @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('24',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ sk_B )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['10','25','26'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','29'])).

thf('31',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('32',plain,(
    ! [X7: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( k6_partfun1 @ X9 )
      = ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X7: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X7 ) @ X7 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','30','35'])).

thf('37',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ sk_B )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

thf('39',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

thf('40',plain,(
    ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('42',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('43',plain,(
    ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.loi7vRZy57
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:16:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 87 iterations in 0.091s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k3_partfun1_type, type, k3_partfun1: $i > $i > $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.36/0.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.36/0.54  thf('0', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.36/0.54  thf(dt_k6_partfun1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( m1_subset_1 @
% 0.36/0.54         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.36/0.54       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X8 : $i]:
% 0.36/0.54         (m1_subset_1 @ (k6_partfun1 @ X8) @ 
% 0.36/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.36/0.54  thf(redefinition_k6_partfun1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.36/0.54  thf('2', plain, (![X9 : $i]: ((k6_partfun1 @ X9) = (k6_relat_1 @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X8 : $i]:
% 0.36/0.54         (m1_subset_1 @ (k6_relat_1 @ X8) @ 
% 0.36/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))),
% 0.36/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['0', '3'])).
% 0.36/0.54  thf(t174_partfun1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( v1_partfun1 @ C @ A ) <=>
% 0.36/0.54         ( ( k5_partfun1 @ A @ B @ C ) = ( k1_tarski @ C ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (v1_partfun1 @ X13 @ X14)
% 0.36/0.54          | ((k5_partfun1 @ X14 @ X15 @ X13) = (k1_tarski @ X13))
% 0.36/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.36/0.54          | ~ (v1_funct_1 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [t174_partfun1])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.36/0.54        | ((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.36/0.54            = (k1_tarski @ k1_xboole_0))
% 0.36/0.54        | ~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.54  thf(t162_funct_2, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.54       ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) ) =
% 0.36/0.54         ( k1_tarski @ B ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.54          ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) ) =
% 0.36/0.54            ( k1_tarski @ B ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t162_funct_2])).
% 0.36/0.54  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc3_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.54       ( ![C:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54           ( v1_xboole_0 @ C ) ) ) ))).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ X4)
% 0.36/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X6)))
% 0.36/0.54          | (v1_xboole_0 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.36/0.54  thf('10', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t161_funct_2, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.54         ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) ) =
% 0.36/0.54           ( k1_tarski @ C ) ) ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         (((X12) = (k1_xboole_0))
% 0.36/0.54          | ~ (v1_funct_1 @ X11)
% 0.36/0.54          | ~ (v1_funct_2 @ X11 @ X10 @ X12)
% 0.36/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 0.36/0.54          | ((k5_partfun1 @ X10 @ X12 @ (k3_partfun1 @ X11 @ X10 @ X12))
% 0.36/0.54              = (k1_tarski @ X11)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t161_funct_2])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      ((((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.36/0.54          = (k1_tarski @ sk_B))
% 0.36/0.54        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.36/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t87_partfun1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( k3_partfun1 @ C @ A @ B ) = ( C ) ) ))).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.54         (((k3_partfun1 @ X16 @ X17 @ X18) = (X16))
% 0.36/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.36/0.54          | ~ (v1_funct_1 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [t87_partfun1])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((~ (v1_funct_1 @ sk_B) | ((k3_partfun1 @ sk_B @ sk_A @ sk_A) = (sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.54  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('18', plain, (((k3_partfun1 @ sk_B @ sk_A @ sk_A) = (sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((((k5_partfun1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.36/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['13', '18', '19', '20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.36/0.54         != (k1_tarski @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('23', plain, (((k3_partfun1 @ sk_B @ sk_A @ sk_A) = (sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (((k5_partfun1 @ sk_A @ sk_A @ sk_B) != (k1_tarski @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.36/0.54  thf('25', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['21', '24'])).
% 0.36/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.54  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('27', plain, ((v1_xboole_0 @ sk_B)),
% 0.36/0.54      inference('demod', [status(thm)], ['10', '25', '26'])).
% 0.36/0.54  thf(l13_xboole_0, axiom,
% 0.36/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.54  thf('29', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('30', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '29'])).
% 0.36/0.54  thf('31', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.36/0.54  thf('32', plain, (![X7 : $i]: (v1_partfun1 @ (k6_partfun1 @ X7) @ X7)),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.36/0.54  thf('33', plain, (![X9 : $i]: ((k6_partfun1 @ X9) = (k6_relat_1 @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.54  thf('34', plain, (![X7 : $i]: (v1_partfun1 @ (k6_relat_1 @ X7) @ X7)),
% 0.36/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.54  thf('35', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('sup+', [status(thm)], ['31', '34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.36/0.54         = (k1_tarski @ k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['6', '30', '35'])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (((k5_partfun1 @ sk_A @ sk_A @ sk_B) != (k1_tarski @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.36/0.54  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['21', '24'])).
% 0.36/0.54  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['21', '24'])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B) != (k1_tarski @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.36/0.54  thf('41', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('42', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (((k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.36/0.54         != (k1_tarski @ k1_xboole_0))),
% 0.36/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.36/0.54  thf('44', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['36', '43'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
