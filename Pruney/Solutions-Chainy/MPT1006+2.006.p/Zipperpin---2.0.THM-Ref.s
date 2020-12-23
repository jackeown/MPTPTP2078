%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EYsT0THG1D

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 119 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  525 ( 824 expanded)
%              Number of equality atoms :   46 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['4','9'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k8_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k10_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['13','16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( v1_funct_2 @ X30 @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('27',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['20','21','24','27','28'])).

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

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('35',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k8_relset_1 @ X19 @ X20 @ X21 @ X20 )
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','37','42'])).

thf('44',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EYsT0THG1D
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 247 iterations in 0.128s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(t60_funct_2, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.20/0.58         ( m1_subset_1 @
% 0.20/0.58           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.20/0.58       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.20/0.58            ( m1_subset_1 @
% 0.20/0.58              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.20/0.58          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t113_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.58  thf('4', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['1', '3'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.58  thf(cc3_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.58       ( ![C:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58           ( v1_xboole_0 @ C ) ) ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.58         (~ (v1_xboole_0 @ X12)
% 0.20/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 0.20/0.58          | (v1_xboole_0 @ X13))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X1 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.58          | (v1_xboole_0 @ X1)
% 0.20/0.58          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.58  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X1 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.58          | (v1_xboole_0 @ X1))),
% 0.20/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.58  thf('10', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.58  thf(l13_xboole_0, axiom,
% 0.20/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('12', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B)
% 0.20/0.58         != (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['0', '12'])).
% 0.20/0.58  thf(t4_subset_1, axiom,
% 0.20/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.20/0.58          | ((k8_relset_1 @ X16 @ X17 @ X15 @ X18) = (k10_relat_1 @ X15 @ X18)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.20/0.58           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.20/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.58  thf('17', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.58  thf(t60_relat_1, axiom,
% 0.20/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.58  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf(t4_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.58       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.58         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.20/0.58           ( m1_subset_1 @
% 0.20/0.58             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (![X30 : $i, X31 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.20/0.58          | (v1_funct_2 @ X30 @ (k1_relat_1 @ X30) @ X31)
% 0.20/0.58          | ~ (v1_funct_1 @ X30)
% 0.20/0.58          | ~ (v1_relat_1 @ X30))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.58          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.58          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.58  thf('21', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.20/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf(cc1_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( v1_relat_1 @ C ) ))).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.58         ((v1_relat_1 @ X9)
% 0.20/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.58  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('26', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf('27', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('28', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.58  thf('29', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.58      inference('demod', [status(thm)], ['20', '21', '24', '27', '28'])).
% 0.20/0.58  thf(d1_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_1, axiom,
% 0.20/0.58    (![C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.58         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.20/0.58          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.20/0.58          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.58          | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.58  thf(zf_stmt_2, axiom,
% 0.20/0.58    (![B:$i,A:$i]:
% 0.20/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X22 : $i, X23 : $i]:
% 0.20/0.58         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.58  thf('33', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.20/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_5, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.58         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.20/0.58          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.20/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['33', '36'])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.58  thf(t38_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.58         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.58  thf('39', plain,
% 0.20/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.58         (((k8_relset_1 @ X19 @ X20 @ X21 @ X20)
% 0.20/0.58            = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.20/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.58      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 0.20/0.58           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.20/0.58           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.20/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.20/0.58           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['31', '37', '42'])).
% 0.20/0.58  thf('44', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.58      inference('demod', [status(thm)], ['17', '43'])).
% 0.20/0.58  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.45/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
