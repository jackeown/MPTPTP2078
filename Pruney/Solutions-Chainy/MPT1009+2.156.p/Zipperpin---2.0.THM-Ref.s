%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wv0f5ZDPib

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 191 expanded)
%              Number of leaves         :   39 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  587 (2358 expanded)
%              Number of equality atoms :   43 ( 127 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('19',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k11_relat_1 @ X21 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k11_relat_1 @ sk_D_1 @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','28','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k11_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k11_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ X14 @ ( k1_tarski @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k11_relat_1 @ sk_D_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('43',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k11_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['31','36','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wv0f5ZDPib
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:12:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.61  % Solved by: fo/fo7.sh
% 0.22/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.61  % done 118 iterations in 0.143s
% 0.22/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.61  % SZS output start Refutation
% 0.22/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.61  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.61  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.22/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.61  thf(t64_funct_2, conjecture,
% 0.22/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.22/0.61         ( m1_subset_1 @
% 0.22/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.22/0.61       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.61         ( r1_tarski @
% 0.22/0.61           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.22/0.61           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.22/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.22/0.61            ( m1_subset_1 @
% 0.22/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.22/0.61          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.61            ( r1_tarski @
% 0.22/0.61              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.22/0.61              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.22/0.61    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.22/0.61  thf('0', plain,
% 0.22/0.61      (~ (r1_tarski @ 
% 0.22/0.61          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.22/0.61          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('1', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf(d1_funct_2, axiom,
% 0.22/0.61    (![A:$i,B:$i,C:$i]:
% 0.22/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.22/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.61  thf(zf_stmt_1, axiom,
% 0.22/0.61    (![C:$i,B:$i,A:$i]:
% 0.22/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.61  thf('2', plain,
% 0.22/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.61         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.22/0.61          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.22/0.61          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.61  thf('3', plain,
% 0.22/0.61      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.61        | ((k1_tarski @ sk_A)
% 0.22/0.61            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 0.22/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.61  thf(zf_stmt_2, axiom,
% 0.22/0.61    (![B:$i,A:$i]:
% 0.22/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.22/0.61  thf('4', plain,
% 0.22/0.61      (![X29 : $i, X30 : $i]:
% 0.22/0.61         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.61  thf('5', plain,
% 0.22/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.22/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.22/0.61  thf(zf_stmt_5, axiom,
% 0.22/0.61    (![A:$i,B:$i,C:$i]:
% 0.22/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.61  thf('6', plain,
% 0.22/0.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.61         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.22/0.61          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.22/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.61  thf('7', plain,
% 0.22/0.61      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.61        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.22/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.61  thf('8', plain,
% 0.22/0.61      ((((sk_B) = (k1_xboole_0))
% 0.22/0.61        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.22/0.61      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.61  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('10', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.61      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.22/0.61  thf('11', plain,
% 0.22/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.22/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.61    (![A:$i,B:$i,C:$i]:
% 0.22/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.61  thf('12', plain,
% 0.22/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.61         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.22/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.22/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.61  thf('13', plain,
% 0.22/0.61      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.22/0.61         = (k1_relat_1 @ sk_D_1))),
% 0.22/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.61  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.22/0.61  thf('15', plain,
% 0.22/0.61      (~ (r1_tarski @ 
% 0.22/0.61          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.22/0.61          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.22/0.61      inference('demod', [status(thm)], ['0', '14'])).
% 0.22/0.61  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.22/0.61  thf(t69_enumset1, axiom,
% 0.22/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.61  thf('17', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.22/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.61  thf(d2_tarski, axiom,
% 0.22/0.61    (![A:$i,B:$i,C:$i]:
% 0.22/0.61     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.61       ( ![D:$i]:
% 0.22/0.61         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.61  thf('18', plain,
% 0.22/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.61         (((X1) != (X0))
% 0.22/0.61          | (r2_hidden @ X1 @ X2)
% 0.22/0.61          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.22/0.61      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.61  thf('19', plain,
% 0.22/0.61      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.22/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.61  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.61      inference('sup+', [status(thm)], ['17', '19'])).
% 0.22/0.61  thf('21', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.61      inference('sup+', [status(thm)], ['16', '20'])).
% 0.22/0.61  thf(t117_funct_1, axiom,
% 0.22/0.61    (![A:$i,B:$i]:
% 0.22/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.61       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.61         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.22/0.61  thf('22', plain,
% 0.22/0.61      (![X20 : $i, X21 : $i]:
% 0.22/0.61         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.22/0.61          | ((k11_relat_1 @ X21 @ X20) = (k1_tarski @ (k1_funct_1 @ X21 @ X20)))
% 0.22/0.61          | ~ (v1_funct_1 @ X21)
% 0.22/0.61          | ~ (v1_relat_1 @ X21))),
% 0.22/0.61      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.22/0.61  thf('23', plain,
% 0.22/0.61      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.61        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.61        | ((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.22/0.61            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.22/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.61  thf('24', plain,
% 0.22/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.22/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf(cc2_relat_1, axiom,
% 0.22/0.61    (![A:$i]:
% 0.22/0.61     ( ( v1_relat_1 @ A ) =>
% 0.22/0.61       ( ![B:$i]:
% 0.22/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.61  thf('25', plain,
% 0.22/0.61      (![X12 : $i, X13 : $i]:
% 0.22/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.22/0.61          | (v1_relat_1 @ X12)
% 0.22/0.61          | ~ (v1_relat_1 @ X13))),
% 0.22/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.61  thf('26', plain,
% 0.22/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.22/0.61        | (v1_relat_1 @ sk_D_1))),
% 0.22/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.61  thf(fc6_relat_1, axiom,
% 0.22/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.61  thf('27', plain,
% 0.22/0.61      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.22/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.61  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.61  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('30', plain,
% 0.22/0.61      (((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.22/0.61         = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.22/0.61      inference('demod', [status(thm)], ['23', '28', '29'])).
% 0.22/0.61  thf('31', plain,
% 0.22/0.61      (~ (r1_tarski @ 
% 0.22/0.61          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.22/0.61          (k11_relat_1 @ sk_D_1 @ sk_A))),
% 0.22/0.61      inference('demod', [status(thm)], ['15', '30'])).
% 0.22/0.61  thf('32', plain,
% 0.22/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.22/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.61  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.22/0.61  thf('34', plain,
% 0.22/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.22/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.22/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.61  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.61       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.61  thf('35', plain,
% 0.22/0.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.22/0.61          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.22/0.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.61  thf('36', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ X0)
% 0.22/0.61           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.61  thf('37', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.22/0.61      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.22/0.61  thf(d16_relat_1, axiom,
% 0.22/0.61    (![A:$i]:
% 0.22/0.61     ( ( v1_relat_1 @ A ) =>
% 0.22/0.61       ( ![B:$i]:
% 0.22/0.61         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.61  thf('38', plain,
% 0.22/0.61      (![X14 : $i, X15 : $i]:
% 0.22/0.61         (((k11_relat_1 @ X14 @ X15) = (k9_relat_1 @ X14 @ (k1_tarski @ X15)))
% 0.22/0.61          | ~ (v1_relat_1 @ X14))),
% 0.22/0.61      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.61  thf('39', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         (((k11_relat_1 @ X0 @ sk_A)
% 0.22/0.61            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D_1)))
% 0.22/0.61          | ~ (v1_relat_1 @ X0))),
% 0.22/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.61  thf(t147_relat_1, axiom,
% 0.22/0.61    (![A:$i,B:$i]:
% 0.22/0.61     ( ( v1_relat_1 @ B ) =>
% 0.22/0.61       ( r1_tarski @
% 0.22/0.61         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.22/0.61  thf('40', plain,
% 0.22/0.61      (![X18 : $i, X19 : $i]:
% 0.22/0.61         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ 
% 0.22/0.61           (k9_relat_1 @ X18 @ (k1_relat_1 @ X18)))
% 0.22/0.61          | ~ (v1_relat_1 @ X18))),
% 0.22/0.61      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.22/0.61  thf('41', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         ((r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 0.22/0.61           (k11_relat_1 @ sk_D_1 @ sk_A))
% 0.22/0.61          | ~ (v1_relat_1 @ sk_D_1)
% 0.22/0.61          | ~ (v1_relat_1 @ sk_D_1))),
% 0.22/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.22/0.61  thf('42', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.61  thf('43', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.61  thf('44', plain,
% 0.22/0.61      (![X0 : $i]:
% 0.22/0.61         (r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ 
% 0.22/0.61          (k11_relat_1 @ sk_D_1 @ sk_A))),
% 0.22/0.61      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.22/0.61  thf('45', plain, ($false),
% 0.22/0.61      inference('demod', [status(thm)], ['31', '36', '44'])).
% 0.22/0.61  
% 0.22/0.61  % SZS output end Refutation
% 0.22/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
