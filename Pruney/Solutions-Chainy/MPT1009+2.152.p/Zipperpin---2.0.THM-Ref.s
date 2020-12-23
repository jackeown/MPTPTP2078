%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jqsSnh2HuS

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 202 expanded)
%              Number of leaves         :   39 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  594 (2459 expanded)
%              Number of equality atoms :   44 ( 130 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X14 @ X15 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k11_relat_1 @ X18 @ X17 )
        = ( k1_tarski @ ( k1_funct_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k11_relat_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k11_relat_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X16: $i] :
      ( ( ( k9_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k11_relat_1 @ X10 @ X11 )
        = ( k9_relat_1 @ X10 @ ( k1_tarski @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('44',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','44'])).

thf('46',plain,(
    ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jqsSnh2HuS
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 69 iterations in 0.081s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(t144_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i]:
% 0.21/0.53         ((r1_tarski @ (k9_relat_1 @ X14 @ X15) @ (k2_relat_1 @ X14))
% 0.21/0.53          | ~ (v1_relat_1 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.21/0.53  thf(t64_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.53         ( m1_subset_1 @
% 0.21/0.53           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53         ( r1_tarski @
% 0.21/0.53           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.21/0.53           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.53            ( m1_subset_1 @
% 0.21/0.53              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53            ( r1_tarski @
% 0.21/0.53              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.21/0.53              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (~ (r1_tarski @ 
% 0.21/0.53          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.21/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d1_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_1, axiom,
% 0.21/0.53    (![C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.21/0.53          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.21/0.53          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.53        | ((k1_tarski @ sk_A)
% 0.21/0.53            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf(zf_stmt_2, axiom,
% 0.21/0.53    (![B:$i,A:$i]:
% 0.21/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_5, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.21/0.53          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.53        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))
% 0.21/0.53        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.53  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (~ (r1_tarski @ 
% 0.21/0.53          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.21/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '15'])).
% 0.21/0.53  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.21/0.53  thf(d1_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.53  thf('20', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.21/0.53      inference('sup+', [status(thm)], ['17', '19'])).
% 0.21/0.53  thf(t117_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.53         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.21/0.53          | ((k11_relat_1 @ X18 @ X17) = (k1_tarski @ (k1_funct_1 @ X18 @ X17)))
% 0.21/0.53          | ~ (v1_funct_1 @ X18)
% 0.21/0.53          | ~ (v1_relat_1 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.53        | ((k11_relat_1 @ sk_D @ sk_A)
% 0.21/0.53            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.21/0.53          | (v1_relat_1 @ X8)
% 0.21/0.53          | ~ (v1_relat_1 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.21/0.53        | (v1_relat_1 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf(fc6_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.53  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((k11_relat_1 @ sk_D @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (~ (r1_tarski @ 
% 0.21/0.53          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.21/0.53          (k11_relat_1 @ sk_D @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.53          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.21/0.53           = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ 
% 0.21/0.53          (k11_relat_1 @ sk_D @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['30', '35'])).
% 0.21/0.53  thf(t146_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X16 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X16 @ (k1_relat_1 @ X16)) = (k2_relat_1 @ X16))
% 0.21/0.53          | ~ (v1_relat_1 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.53  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.21/0.53  thf(d16_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         (((k11_relat_1 @ X10 @ X11) = (k9_relat_1 @ X10 @ (k1_tarski @ X11)))
% 0.21/0.53          | ~ (v1_relat_1 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_D)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.53      inference('sup+', [status(thm)], ['37', '40'])).
% 0.21/0.53  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('44', plain, (((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['36', '44'])).
% 0.21/0.53  thf('46', plain, (~ (v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '45'])).
% 0.21/0.53  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('48', plain, ($false), inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
