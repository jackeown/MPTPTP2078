%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.94YbgjH09v

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 136 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  545 (1836 expanded)
%              Number of equality atoms :   47 ( 138 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t50_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k10_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X30 ) ) )
      | ( ( k8_relset_1 @ X28 @ X30 @ X29 @ X30 )
        = X28 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('11',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ sk_B )
      = sk_A )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_B )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ ( k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('24',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['22','29','30','31'])).

thf('33',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('34',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['17','34'])).

thf('36',plain,
    ( ( k10_relat_1 @ sk_D @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['15','35'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('38',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( r1_tarski @ X15 @ ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('50',plain,(
    r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['8','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.94YbgjH09v
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 104 iterations in 0.047s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.56  thf(t50_funct_2, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.56       ( ( r1_tarski @ C @ A ) =>
% 0.20/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.56           ( r1_tarski @
% 0.20/0.56             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.56          ( ( r1_tarski @ C @ A ) =>
% 0.20/0.56            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.56              ( r1_tarski @
% 0.20/0.56                C @ 
% 0.20/0.56                ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t50_funct_2])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (~ (r1_tarski @ sk_C @ 
% 0.20/0.56          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ 
% 0.20/0.56           (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.56          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (~ (r1_tarski @ sk_C @ 
% 0.20/0.56          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.20/0.56          | ((k8_relset_1 @ X25 @ X26 @ X24 @ X27) = (k10_relat_1 @ X24 @ X27)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t48_funct_2, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.56         (((X30) = (k1_xboole_0))
% 0.20/0.56          | ~ (v1_funct_1 @ X29)
% 0.20/0.56          | ~ (v1_funct_2 @ X29 @ X28 @ X30)
% 0.20/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X30)))
% 0.20/0.56          | ((k8_relset_1 @ X28 @ X30 @ X29 @ X30) = (X28)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      ((((k8_relset_1 @ sk_A @ sk_B @ sk_D @ sk_B) = (sk_A))
% 0.20/0.56        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.20/0.56        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      ((((k10_relat_1 @ sk_D @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.20/0.56  thf('16', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.56      inference('split', [status(esa)], ['16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('split', [status(esa)], ['16'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (~ (r1_tarski @ sk_C @ 
% 0.20/0.56          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ 
% 0.20/0.56           (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      ((~ (r1_tarski @ sk_C @ 
% 0.20/0.56           (k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ 
% 0.20/0.56            (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C))))
% 0.20/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('split', [status(esa)], ['16'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      ((~ (r1_tarski @ sk_C @ 
% 0.20/0.56           (k8_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ 
% 0.20/0.56            (k7_relset_1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C))))
% 0.20/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('split', [status(esa)], ['16'])).
% 0.20/0.56  thf('24', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.56  thf(d10_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i, X2 : $i]:
% 0.20/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 0.20/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.56  thf('28', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('31', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.56  thf('32', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '29', '30', '31'])).
% 0.20/0.56  thf('33', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.56      inference('split', [status(esa)], ['16'])).
% 0.20/0.56  thf('34', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['17', '34'])).
% 0.20/0.56  thf('36', plain, (((k10_relat_1 @ sk_D @ sk_B) = (sk_A))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['15', '35'])).
% 0.20/0.56  thf(t167_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ B ) =>
% 0.20/0.56       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 0.20/0.56          | ~ (v1_relat_1 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.56      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( v1_relat_1 @ C ) ))).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.56         ((v1_relat_1 @ X17)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.56  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.56  thf('42', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.20/0.56      inference('demod', [status(thm)], ['38', '41'])).
% 0.20/0.56  thf('43', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t1_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.56       ( r1_tarski @ A @ C ) ))).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.56          | ~ (r1_tarski @ X4 @ X5)
% 0.20/0.56          | (r1_tarski @ X3 @ X5))),
% 0.20/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.56  thf('46', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '45'])).
% 0.20/0.56  thf(t146_funct_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ B ) =>
% 0.20/0.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.56         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i]:
% 0.20/0.56         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.20/0.56          | (r1_tarski @ X15 @ (k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)))
% 0.20/0.56          | ~ (v1_relat_1 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.56        | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.56  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['8', '50'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
