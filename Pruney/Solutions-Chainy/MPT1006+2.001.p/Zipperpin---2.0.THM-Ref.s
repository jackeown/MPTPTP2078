%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yc7KWZ3Lj4

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:06 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 132 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  540 ( 844 expanded)
%              Number of equality atoms :   45 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','3'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('7',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('8',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','14'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k8_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k10_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X22 ) ) )
      | ( v1_partfun1 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('23',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','10'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_partfun1 @ X17 @ X18 )
      | ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('32',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','33'])).

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

thf('35',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relset_1 @ X14 @ X15 @ X16 @ X15 )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
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

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','48'])).

thf('50',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['19','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yc7KWZ3Lj4
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:14:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 192 iterations in 0.136s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.59  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.41/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.59  thf(t60_funct_2, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.41/0.59         ( m1_subset_1 @
% 0.41/0.59           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.41/0.59       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.41/0.59            ( m1_subset_1 @
% 0.41/0.59              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.41/0.59          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (((k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t113_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i]:
% 0.41/0.59         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.41/0.59  thf('4', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['1', '3'])).
% 0.41/0.59  thf(cc1_subset_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X5 : $i, X6 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.41/0.59          | (v1_xboole_0 @ X5)
% 0.41/0.59          | ~ (v1_xboole_0 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.41/0.59  thf('6', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.41/0.59  thf('7', plain, ((v1_xboole_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.41/0.59  thf('8', plain, ((v1_xboole_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.41/0.59  thf(l13_xboole_0, axiom,
% 0.41/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.59  thf('10', plain, (((sk_A) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.59  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('demod', [status(thm)], ['7', '10'])).
% 0.41/0.59  thf('12', plain, ((v1_xboole_0 @ sk_C)),
% 0.41/0.59      inference('demod', [status(thm)], ['6', '11'])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.59  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (((k8_relset_1 @ k1_xboole_0 @ sk_A_1 @ k1_xboole_0 @ sk_B)
% 0.41/0.59         != (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['0', '14'])).
% 0.41/0.59  thf(t4_subset_1, axiom,
% 0.41/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.59  thf(redefinition_k8_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.41/0.59          | ((k8_relset_1 @ X11 @ X12 @ X10 @ X13) = (k10_relat_1 @ X10 @ X13)))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.41/0.59           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['15', '18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.41/0.59  thf(cc1_partfun1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.41/0.59       ( ![C:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ X20)
% 0.41/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X22)))
% 0.41/0.59          | (v1_partfun1 @ X21 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X1 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.41/0.59          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.41/0.59          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('demod', [status(thm)], ['7', '10'])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X1 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.41/0.59          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.59  thf('26', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('sup-', [status(thm)], ['20', '25'])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.59  thf(cc1_funct_2, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.41/0.59         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.59         (~ (v1_funct_1 @ X17)
% 0.41/0.59          | ~ (v1_partfun1 @ X17 @ X18)
% 0.41/0.59          | (v1_funct_2 @ X17 @ X18 @ X19)
% 0.41/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.41/0.59          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 0.41/0.59          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.59  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('31', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('32', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.41/0.59          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 0.41/0.59      inference('demod', [status(thm)], ['29', '32'])).
% 0.41/0.59  thf('34', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.41/0.59      inference('sup-', [status(thm)], ['26', '33'])).
% 0.41/0.59  thf(d1_funct_2, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_1, axiom,
% 0.41/0.59    (![C:$i,B:$i,A:$i]:
% 0.41/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.59         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.41/0.59          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.41/0.59          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.41/0.59          | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.59  thf(t38_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.41/0.59         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.59         (((k8_relset_1 @ X14 @ X15 @ X16 @ X15)
% 0.41/0.59            = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.41/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.41/0.59      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X0)
% 0.41/0.59           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.41/0.59           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.41/0.59           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.41/0.59          | ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['36', '41'])).
% 0.41/0.59  thf(zf_stmt_2, axiom,
% 0.41/0.59    (![B:$i,A:$i]:
% 0.41/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i]:
% 0.41/0.59         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.59  thf('44', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.41/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.59  thf(zf_stmt_5, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.59         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.41/0.59          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.41/0.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.41/0.59      inference('sup-', [status(thm)], ['44', '47'])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['42', '48'])).
% 0.41/0.59  thf('50', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.41/0.59      inference('demod', [status(thm)], ['19', '49'])).
% 0.41/0.59  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
