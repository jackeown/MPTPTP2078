%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pXt33tDvBA

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:48 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 216 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  633 (2887 expanded)
%              Number of equality atoms :   58 ( 227 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('1',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('16',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_relat_1 @ X12 )
       != ( k1_tarski @ X11 ) )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_tarski @ ( k1_funct_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf('28',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t45_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X30 ) ) )
      | ( ( k7_relset_1 @ X28 @ X30 @ X29 @ X28 )
        = ( k2_relset_1 @ X28 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t45_funct_2])).

thf('33',plain,
    ( ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ ( k1_relat_1 @ sk_C ) )
      = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k7_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k9_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
      = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36','39','40'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['28','43'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('47',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pXt33tDvBA
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 95 iterations in 0.132s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.58  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.58  thf(t146_relat_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ A ) =>
% 0.41/0.58       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      (![X10 : $i]:
% 0.41/0.58         (((k9_relat_1 @ X10 @ (k1_relat_1 @ X10)) = (k2_relat_1 @ X10))
% 0.41/0.58          | ~ (v1_relat_1 @ X10))),
% 0.41/0.58      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.41/0.58  thf(t62_funct_2, conjecture,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.58         ( m1_subset_1 @
% 0.41/0.58           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.58       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.58         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.41/0.58           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.58            ( m1_subset_1 @
% 0.41/0.58              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.58          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.58            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.41/0.58              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.41/0.58         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('2', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(d1_funct_2, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_1, axiom,
% 0.41/0.58    (![C:$i,B:$i,A:$i]:
% 0.41/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.58         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.41/0.58          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.41/0.58          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.41/0.58        | ((k1_tarski @ sk_A)
% 0.41/0.58            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.58  thf(zf_stmt_2, axiom,
% 0.41/0.58    (![B:$i,A:$i]:
% 0.41/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X20 : $i, X21 : $i]:
% 0.41/0.58         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.58  thf(zf_stmt_5, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.58         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.41/0.58          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.41/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.41/0.58        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      ((((sk_B) = (k1_xboole_0))
% 0.41/0.58        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['5', '8'])).
% 0.41/0.58  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('11', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.58         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.41/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.41/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.58  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C)
% 0.41/0.58         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['1', '15'])).
% 0.41/0.58  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.41/0.58  thf(t14_funct_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.58       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.41/0.58         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (![X11 : $i, X12 : $i]:
% 0.41/0.58         (((k1_relat_1 @ X12) != (k1_tarski @ X11))
% 0.41/0.58          | ((k2_relat_1 @ X12) = (k1_tarski @ (k1_funct_1 @ X12 @ X11)))
% 0.41/0.58          | ~ (v1_funct_1 @ X12)
% 0.41/0.58          | ~ (v1_relat_1 @ X12))),
% 0.41/0.58      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.41/0.58          | ~ (v1_relat_1 @ X0)
% 0.41/0.58          | ~ (v1_funct_1 @ X0)
% 0.41/0.58          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.58  thf('20', plain,
% 0.41/0.58      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.41/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.41/0.58      inference('eq_res', [status(thm)], ['19'])).
% 0.41/0.58  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(cc2_relat_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X6 : $i, X7 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.41/0.58          | (v1_relat_1 @ X6)
% 0.41/0.58          | ~ (v1_relat_1 @ X7))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.41/0.58        | (v1_relat_1 @ sk_C))),
% 0.41/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.58  thf(fc6_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.41/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.58  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('27', plain,
% 0.41/0.58      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['20', '21', '26'])).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C)
% 0.41/0.58         != (k2_relat_1 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['16', '27'])).
% 0.41/0.58  thf('29', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.41/0.58  thf('31', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.41/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.58  thf(t45_funct_2, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.58         ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.58  thf('32', plain,
% 0.41/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.58         (((X30) = (k1_xboole_0))
% 0.41/0.58          | ~ (v1_funct_1 @ X29)
% 0.41/0.58          | ~ (v1_funct_2 @ X29 @ X28 @ X30)
% 0.41/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X30)))
% 0.41/0.58          | ((k7_relset_1 @ X28 @ X30 @ X29 @ X28)
% 0.41/0.58              = (k2_relset_1 @ X28 @ X30 @ X29)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t45_funct_2])).
% 0.41/0.58  thf('33', plain,
% 0.41/0.58      ((((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ (k1_relat_1 @ sk_C))
% 0.41/0.58          = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))
% 0.41/0.58        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.41/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_C @ 
% 0.41/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.41/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.58  thf(redefinition_k7_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.41/0.58          | ((k7_relset_1 @ X17 @ X18 @ X16 @ X19) = (k9_relat_1 @ X16 @ X19)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C @ X0)
% 0.41/0.58           = (k9_relat_1 @ sk_C @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.58  thf('37', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.41/0.58  thf('39', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.41/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.58  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.41/0.58          = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))
% 0.41/0.58        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['33', '36', '39', '40'])).
% 0.41/0.58  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('43', plain,
% 0.41/0.58      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.41/0.58         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ sk_C))),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.41/0.58  thf('44', plain,
% 0.41/0.58      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['28', '43'])).
% 0.41/0.58  thf('45', plain,
% 0.41/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.41/0.58      inference('sup-', [status(thm)], ['0', '44'])).
% 0.41/0.58  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('47', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.41/0.58  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
