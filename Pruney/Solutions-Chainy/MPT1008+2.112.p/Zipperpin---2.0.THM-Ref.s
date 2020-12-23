%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kxt1zKnWDl

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 211 expanded)
%              Number of leaves         :   38 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  622 (2714 expanded)
%              Number of equality atoms :   52 ( 209 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

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
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('16',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ ( k1_tarski @ X14 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('30',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','27','28','29'])).

thf('31',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 )
 != ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['16','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k7_relset_1 @ X23 @ X24 @ X25 @ X23 )
        = ( k2_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('36',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
 != ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['31','40'])).

thf('42',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
     != ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('44',plain,(
    ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
 != ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kxt1zKnWDl
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 114 iterations in 0.088s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(t148_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.20/0.54          | ~ (v1_relat_1 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf(t62_funct_2, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.54         ( m1_subset_1 @
% 0.20/0.54           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.54         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.54           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.54            ( m1_subset_1 @
% 0.20/0.54              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.54            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.54              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.20/0.54         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('2', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d1_funct_2, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, axiom,
% 0.20/0.54    (![C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.54         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.20/0.54          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.20/0.54          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.54        | ((k1_tarski @ sk_A)
% 0.20/0.54            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(zf_stmt_2, axiom,
% 0.20/0.54    (![B:$i,A:$i]:
% 0.20/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_5, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.54         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.20/0.54          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.20/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.54        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0))
% 0.20/0.54        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.54  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.54         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.20/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.20/0.54         = (k1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1)
% 0.20/0.54         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['1', '15'])).
% 0.20/0.54  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.20/0.54  thf(d1_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.54  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.54  thf('20', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['17', '19'])).
% 0.20/0.54  thf(t168_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.54         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.20/0.54           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.20/0.54          | ((k2_relat_1 @ (k7_relat_1 @ X15 @ (k1_tarski @ X14)))
% 0.20/0.54              = (k1_tarski @ (k1_funct_1 @ X15 @ X14)))
% 0.20/0.54          | ~ (v1_funct_1 @ X15)
% 0.20/0.54          | ~ (v1_relat_1 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [t168_funct_1])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.54        | ((k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.20/0.54            = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.54          | (v1_relat_1 @ X8)
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.54        | (v1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf(fc6_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.54  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (((k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.54         = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['22', '27', '28', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1)
% 0.20/0.54         != (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf(t38_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.54         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.54         (((k7_relset_1 @ X23 @ X24 @ X25 @ X23)
% 0.20/0.54            = (k2_relset_1 @ X23 @ X24 @ X25))
% 0.20/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (((k7_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ 
% 0.20/0.54         (k1_relat_1 @ sk_C_1))
% 0.20/0.54         = (k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.54          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k7_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ X0)
% 0.20/0.54           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.54         = (k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['36', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.54         != (k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))))),
% 0.20/0.54      inference('demod', [status(thm)], ['31', '40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      ((((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.54          != (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '41'])).
% 0.20/0.54  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.54         != (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.54  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
