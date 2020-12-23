%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lYsktf7iDv

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:02 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 242 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  632 (3317 expanded)
%              Number of equality atoms :   47 ( 183 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k7_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k9_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
       != ( k1_tarski @ X5 ) )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_tarski @ ( k1_funct_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k7_relset_1 @ X20 @ X21 @ X22 @ X20 )
        = ( k2_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('34',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('40',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X3 @ X4 ) @ ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['27','28'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['31','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lYsktf7iDv
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 77 iterations in 0.132s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.59  thf(t64_funct_2, conjecture,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.59         ( m1_subset_1 @
% 0.37/0.59           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.59         ( r1_tarski @
% 0.37/0.59           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.37/0.59           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.59            ( m1_subset_1 @
% 0.37/0.59              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.59            ( r1_tarski @
% 0.37/0.59              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.37/0.59              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (~ (r1_tarski @ 
% 0.37/0.59          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.37/0.59          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(d1_funct_2, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_1, axiom,
% 0.37/0.59    (![C:$i,B:$i,A:$i]:
% 0.37/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.59         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.37/0.59          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.37/0.59          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.37/0.59        | ((k1_tarski @ sk_A)
% 0.37/0.59            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf(zf_stmt_2, axiom,
% 0.37/0.59    (![B:$i,A:$i]:
% 0.37/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (![X23 : $i, X24 : $i]:
% 0.37/0.59         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.59  thf(zf_stmt_5, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.59         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.37/0.59          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.37/0.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.37/0.59        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      ((((sk_B) = (k1_xboole_0))
% 0.37/0.59        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.59         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.37/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.59  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (~ (r1_tarski @ 
% 0.37/0.59          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.37/0.59          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['0', '14'])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf(redefinition_k7_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.37/0.59          | ((k7_relset_1 @ X17 @ X18 @ X16 @ X19) = (k9_relat_1 @ X16 @ X19)))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.37/0.59           = (k9_relat_1 @ sk_D @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.37/0.59          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['15', '20'])).
% 0.37/0.59  thf('22', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.37/0.59  thf(t14_funct_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.59       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.37/0.59         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (![X5 : $i, X6 : $i]:
% 0.37/0.59         (((k1_relat_1 @ X6) != (k1_tarski @ X5))
% 0.37/0.59          | ((k2_relat_1 @ X6) = (k1_tarski @ (k1_funct_1 @ X6 @ X5)))
% 0.37/0.59          | ~ (v1_funct_1 @ X6)
% 0.37/0.59          | ~ (v1_relat_1 @ X6))),
% 0.37/0.59      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.37/0.59          | ~ (v1_relat_1 @ X0)
% 0.37/0.59          | ~ (v1_funct_1 @ X0)
% 0.37/0.59          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.37/0.59        | ~ (v1_funct_1 @ sk_D)
% 0.37/0.59        | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.59      inference('eq_res', [status(thm)], ['24'])).
% 0.37/0.59  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(cc1_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( v1_relat_1 @ C ) ))).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.59         ((v1_relat_1 @ X7)
% 0.37/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.37/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.59  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.37/0.59  thf('31', plain,
% 0.37/0.59      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['21', '30'])).
% 0.37/0.59  thf('32', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf(t38_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.37/0.59         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.59  thf('33', plain,
% 0.37/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.59         (((k7_relset_1 @ X20 @ X21 @ X22 @ X20)
% 0.37/0.59            = (k2_relset_1 @ X20 @ X21 @ X22))
% 0.37/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.59      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.37/0.59  thf('34', plain,
% 0.37/0.59      (((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ (k1_relat_1 @ sk_D))
% 0.37/0.59         = (k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.59  thf('35', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.37/0.59           = (k9_relat_1 @ sk_D @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.59  thf('36', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.59         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.37/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.59  thf('39', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.59  thf('41', plain,
% 0.37/0.59      (((k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (k2_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['34', '35', '40'])).
% 0.37/0.59  thf(t147_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ B ) =>
% 0.37/0.59       ( r1_tarski @
% 0.37/0.59         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.37/0.59  thf('42', plain,
% 0.37/0.59      (![X3 : $i, X4 : $i]:
% 0.37/0.59         ((r1_tarski @ (k9_relat_1 @ X3 @ X4) @ 
% 0.37/0.59           (k9_relat_1 @ X3 @ (k1_relat_1 @ X3)))
% 0.37/0.59          | ~ (v1_relat_1 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.37/0.59  thf('43', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.37/0.59          | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.59      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.59  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.59  thf('45', plain,
% 0.37/0.59      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.59  thf('46', plain, ($false), inference('demod', [status(thm)], ['31', '45'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
