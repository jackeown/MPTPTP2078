%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6pnbVdGXeg

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:01 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 190 expanded)
%              Number of leaves         :   38 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  579 (2399 expanded)
%              Number of equality atoms :   44 ( 130 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

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

thf('1',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
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
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( ( k11_relat_1 @ X14 @ X13 )
        = ( k1_tarski @ ( k1_funct_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k11_relat_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k11_relat_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k11_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ X8 @ ( k1_tarski @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('42',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,(
    ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6pnbVdGXeg
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 69 iterations in 0.087s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.54  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.35/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.54  thf(t144_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i]:
% 0.35/0.54         ((r1_tarski @ (k9_relat_1 @ X10 @ X11) @ (k2_relat_1 @ X10))
% 0.35/0.54          | ~ (v1_relat_1 @ X10))),
% 0.35/0.54      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.35/0.54  thf(t64_funct_2, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.54         ( m1_subset_1 @
% 0.35/0.54           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.54         ( r1_tarski @
% 0.35/0.54           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.35/0.54           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.54            ( m1_subset_1 @
% 0.35/0.54              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.54            ( r1_tarski @
% 0.35/0.54              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.35/0.54              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (~ (r1_tarski @ 
% 0.35/0.54          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.35/0.54          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('2', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d1_funct_2, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_1, axiom,
% 0.35/0.54    (![C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.35/0.54         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.35/0.54          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.35/0.54          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.35/0.54        | ((k1_tarski @ sk_A)
% 0.35/0.54            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf(zf_stmt_2, axiom,
% 0.35/0.54    (![B:$i,A:$i]:
% 0.35/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X25 : $i, X26 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_5, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.35/0.54         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.35/0.54          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.35/0.54          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.35/0.54        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      ((((sk_B) = (k1_xboole_0))
% 0.35/0.54        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['5', '8'])).
% 0.35/0.54  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('11', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.54         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (~ (r1_tarski @ 
% 0.35/0.54          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.35/0.54          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['1', '15'])).
% 0.35/0.54  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.35/0.54  thf(d1_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.35/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.54  thf('20', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('sup+', [status(thm)], ['17', '19'])).
% 0.35/0.54  thf(t117_funct_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.54         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.35/0.54          | ((k11_relat_1 @ X14 @ X13) = (k1_tarski @ (k1_funct_1 @ X14 @ X13)))
% 0.35/0.54          | ~ (v1_funct_1 @ X14)
% 0.35/0.54          | ~ (v1_relat_1 @ X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.35/0.54        | ~ (v1_funct_1 @ sk_D)
% 0.35/0.54        | ((k11_relat_1 @ sk_D @ sk_A)
% 0.35/0.54            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( v1_relat_1 @ C ) ))).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         ((v1_relat_1 @ X15)
% 0.35/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.54  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.54  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (((k11_relat_1 @ sk_D @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (~ (r1_tarski @ 
% 0.35/0.54          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.35/0.54          (k11_relat_1 @ sk_D @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['16', '27'])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.35/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.35/0.54          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.35/0.54           = (k9_relat_1 @ sk_D @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ 
% 0.35/0.54          (k11_relat_1 @ sk_D @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['28', '33'])).
% 0.35/0.54  thf(t146_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      (![X12 : $i]:
% 0.35/0.54         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 0.35/0.54          | ~ (v1_relat_1 @ X12))),
% 0.35/0.54      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.35/0.54  thf('36', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.35/0.54  thf(d16_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i]:
% 0.35/0.54         (((k11_relat_1 @ X8 @ X9) = (k9_relat_1 @ X8 @ (k1_tarski @ X9)))
% 0.35/0.54          | ~ (v1_relat_1 @ X8))),
% 0.35/0.54      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D)))
% 0.35/0.54          | ~ (v1_relat_1 @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['36', '37'])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      ((((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))
% 0.35/0.54        | ~ (v1_relat_1 @ sk_D)
% 0.35/0.54        | ~ (v1_relat_1 @ sk_D))),
% 0.35/0.54      inference('sup+', [status(thm)], ['35', '38'])).
% 0.35/0.54  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.54  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.54  thf('42', plain, (((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['34', '42'])).
% 0.35/0.54  thf('44', plain, (~ (v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['0', '43'])).
% 0.35/0.54  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.54  thf('46', plain, ($false), inference('demod', [status(thm)], ['44', '45'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
