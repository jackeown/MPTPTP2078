%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWZDUeuxv1

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:43 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 105 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  626 (1276 expanded)
%              Number of equality atoms :   53 (  99 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k8_relset_1 @ X22 @ X23 @ X24 @ ( k7_relset_1 @ X22 @ X23 @ X24 @ X22 ) )
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('3',plain,
    ( ( k8_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ ( k1_tarski @ sk_A ) ) )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relset_1 @ X19 @ X20 @ X21 @ X19 )
        = ( k2_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('6',plain,
    ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k8_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k10_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['3','10','13','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != ( k1_tarski @ X7 ) )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_tarski @ ( k1_funct_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('39',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWZDUeuxv1
% 0.14/0.38  % Computer   : n002.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 17:58:52 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.53/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.76  % Solved by: fo/fo7.sh
% 0.53/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.76  % done 158 iterations in 0.271s
% 0.53/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.76  % SZS output start Refutation
% 0.53/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.53/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.53/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.53/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.53/0.76  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.53/0.76  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.53/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.76  thf(t169_relat_1, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( v1_relat_1 @ A ) =>
% 0.53/0.76       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.53/0.76  thf('0', plain,
% 0.53/0.76      (![X6 : $i]:
% 0.53/0.76         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.53/0.76          | ~ (v1_relat_1 @ X6))),
% 0.53/0.76      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.53/0.76  thf(t62_funct_2, conjecture,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.53/0.76         ( m1_subset_1 @
% 0.53/0.76           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.53/0.76       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.53/0.76         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.53/0.76           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.53/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.53/0.76            ( m1_subset_1 @
% 0.53/0.76              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.53/0.76          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.53/0.76            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.53/0.76              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.53/0.76    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.53/0.76  thf('1', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ 
% 0.53/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t39_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.53/0.76       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.53/0.76           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.53/0.76         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.53/0.76           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.53/0.76  thf('2', plain,
% 0.53/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.76         (((k8_relset_1 @ X22 @ X23 @ X24 @ 
% 0.53/0.76            (k7_relset_1 @ X22 @ X23 @ X24 @ X22))
% 0.53/0.76            = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.53/0.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.53/0.76      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.53/0.76  thf('3', plain,
% 0.53/0.76      (((k8_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ 
% 0.53/0.76         (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ (k1_tarski @ sk_A)))
% 0.53/0.76         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 0.53/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.76  thf('4', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ 
% 0.53/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t38_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.53/0.76         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.53/0.76  thf('5', plain,
% 0.53/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.76         (((k7_relset_1 @ X19 @ X20 @ X21 @ X19)
% 0.53/0.76            = (k2_relset_1 @ X19 @ X20 @ X21))
% 0.53/0.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.53/0.76      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.53/0.76  thf('6', plain,
% 0.53/0.76      (((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ (k1_tarski @ sk_A))
% 0.53/0.76         = (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 0.53/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.53/0.76  thf('7', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ 
% 0.53/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(redefinition_k2_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.53/0.76  thf('8', plain,
% 0.53/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.76         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.53/0.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.53/0.76  thf('9', plain,
% 0.53/0.76      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.53/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.76  thf('10', plain,
% 0.53/0.76      (((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ (k1_tarski @ sk_A))
% 0.53/0.76         = (k2_relat_1 @ sk_C))),
% 0.53/0.76      inference('demod', [status(thm)], ['6', '9'])).
% 0.53/0.76  thf('11', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ 
% 0.53/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(redefinition_k8_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.53/0.76  thf('12', plain,
% 0.53/0.76      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.53/0.76          | ((k8_relset_1 @ X16 @ X17 @ X15 @ X18) = (k10_relat_1 @ X15 @ X18)))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.53/0.76  thf('13', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         ((k8_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ X0)
% 0.53/0.76           = (k10_relat_1 @ sk_C @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.76  thf('14', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(d1_funct_2, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.53/0.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.53/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.53/0.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.53/0.76  thf(zf_stmt_1, axiom,
% 0.53/0.76    (![C:$i,B:$i,A:$i]:
% 0.53/0.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.53/0.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.53/0.76  thf('15', plain,
% 0.53/0.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.53/0.76         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.53/0.76          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.53/0.76          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.76  thf('16', plain,
% 0.53/0.76      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.53/0.76        | ((k1_tarski @ sk_A)
% 0.53/0.76            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.76  thf(zf_stmt_2, axiom,
% 0.53/0.76    (![B:$i,A:$i]:
% 0.53/0.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.76       ( zip_tseitin_0 @ B @ A ) ))).
% 0.53/0.76  thf('17', plain,
% 0.53/0.76      (![X25 : $i, X26 : $i]:
% 0.53/0.76         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.76  thf('18', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ 
% 0.53/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.53/0.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.53/0.76  thf(zf_stmt_5, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.53/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.53/0.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.53/0.76  thf('19', plain,
% 0.53/0.76      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.53/0.76         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.53/0.76          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.53/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.53/0.76  thf('20', plain,
% 0.53/0.76      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.53/0.76        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.53/0.76  thf('21', plain,
% 0.53/0.76      ((((sk_B) = (k1_xboole_0))
% 0.53/0.76        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['17', '20'])).
% 0.53/0.76  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('23', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.53/0.76      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.53/0.76  thf('24', plain,
% 0.53/0.76      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 0.53/0.76      inference('demod', [status(thm)], ['16', '23'])).
% 0.53/0.76  thf('25', plain,
% 0.53/0.76      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_tarski @ sk_A))),
% 0.53/0.76      inference('demod', [status(thm)], ['3', '10', '13', '24'])).
% 0.53/0.76  thf('26', plain,
% 0.53/0.76      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)) | ~ (v1_relat_1 @ sk_C))),
% 0.53/0.76      inference('sup+', [status(thm)], ['0', '25'])).
% 0.53/0.76  thf('27', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ 
% 0.53/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(cc1_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( v1_relat_1 @ C ) ))).
% 0.53/0.76  thf('28', plain,
% 0.53/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.76         ((v1_relat_1 @ X9)
% 0.53/0.76          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.53/0.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.53/0.76  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.76  thf('30', plain, (((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))),
% 0.53/0.76      inference('demod', [status(thm)], ['26', '29'])).
% 0.53/0.76  thf(t14_funct_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.76       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.53/0.76         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.53/0.76  thf('31', plain,
% 0.53/0.76      (![X7 : $i, X8 : $i]:
% 0.53/0.76         (((k1_relat_1 @ X8) != (k1_tarski @ X7))
% 0.53/0.76          | ((k2_relat_1 @ X8) = (k1_tarski @ (k1_funct_1 @ X8 @ X7)))
% 0.53/0.76          | ~ (v1_funct_1 @ X8)
% 0.53/0.76          | ~ (v1_relat_1 @ X8))),
% 0.53/0.76      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.53/0.76  thf('32', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.53/0.76          | ~ (v1_relat_1 @ X0)
% 0.53/0.76          | ~ (v1_funct_1 @ X0)
% 0.53/0.76          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.76  thf('33', plain,
% 0.53/0.76      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.53/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.53/0.76        | ~ (v1_relat_1 @ sk_C))),
% 0.53/0.76      inference('eq_res', [status(thm)], ['32'])).
% 0.53/0.76  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.76  thf('36', plain,
% 0.53/0.76      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.53/0.76      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.53/0.76  thf('37', plain,
% 0.53/0.76      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.53/0.76         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('38', plain,
% 0.53/0.76      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.53/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.76  thf('39', plain,
% 0.53/0.76      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.53/0.76      inference('demod', [status(thm)], ['37', '38'])).
% 0.53/0.76  thf('40', plain, ($false),
% 0.53/0.76      inference('simplify_reflect-', [status(thm)], ['36', '39'])).
% 0.53/0.76  
% 0.53/0.76  % SZS output end Refutation
% 0.53/0.76  
% 0.53/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
