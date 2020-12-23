%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z1ZyvSUsgt

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:24 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 118 expanded)
%              Number of leaves         :   36 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  621 (1084 expanded)
%              Number of equality atoms :   45 (  79 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X8 )
        = ( k1_tarski @ X6 ) )
      | ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( zip_tseitin_0 @ ( k2_tarski @ X1 @ X1 ) @ X3 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X9 ) @ X11 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( k1_tarski @ X1 ) @ X2 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X2 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['6','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','26','29'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X23 ) @ X21 )
      | ( X23
       != ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( k1_funct_1 @ X21 @ X20 ) ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ sk_C @ ( k1_funct_1 @ sk_D @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14 = X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ ( k1_tarski @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('45',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z1ZyvSUsgt
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:01:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 120 iterations in 0.158s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.62  thf(t65_funct_2, conjecture,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.37/0.62         ( m1_subset_1 @
% 0.37/0.62           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.37/0.62       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.37/0.62            ( m1_subset_1 @
% 0.37/0.62              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.37/0.62          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.37/0.62  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(d1_funct_2, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_1, axiom,
% 0.37/0.62    (![C:$i,B:$i,A:$i]:
% 0.37/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.62         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.37/0.62          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.37/0.62          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      ((~ (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.37/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ 
% 0.37/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.62  thf(zf_stmt_4, axiom,
% 0.37/0.62    (![B:$i,A:$i]:
% 0.37/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.62  thf(zf_stmt_5, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.62         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.37/0.62          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.37/0.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.62  thf('6', plain,
% 0.37/0.62      (((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.37/0.62        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.62  thf(t69_enumset1, axiom,
% 0.37/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.62  thf('7', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      (![X30 : $i, X31 : $i]:
% 0.37/0.62         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.37/0.62  thf('9', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.62  thf(l33_zfmisc_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.62       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X6 : $i, X8 : $i]:
% 0.37/0.62         (((k4_xboole_0 @ (k1_tarski @ X6) @ X8) = (k1_tarski @ X6))
% 0.37/0.62          | (r2_hidden @ X6 @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.37/0.62  thf(l35_zfmisc_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.62       ( r2_hidden @ A @ B ) ))).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      (![X9 : $i, X10 : $i]:
% 0.37/0.62         ((r2_hidden @ X9 @ X10)
% 0.37/0.62          | ((k4_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0)))),
% 0.37/0.62      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.37/0.62          | (r2_hidden @ X0 @ X1)
% 0.37/0.62          | (r2_hidden @ X0 @ X1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r2_hidden @ X0 @ X1) | ((k1_tarski @ X0) != (k1_xboole_0)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k2_tarski @ X0 @ X0) != (k1_xboole_0)) | (r2_hidden @ X0 @ X1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['9', '13'])).
% 0.37/0.62  thf('15', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         (((k2_tarski @ X1 @ X1) != (X0))
% 0.37/0.62          | (zip_tseitin_0 @ X0 @ X3)
% 0.37/0.62          | (r2_hidden @ X1 @ X2))),
% 0.37/0.62      inference('sup-', [status(thm)], ['8', '14'])).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         ((r2_hidden @ X1 @ X2) | (zip_tseitin_0 @ (k2_tarski @ X1 @ X1) @ X3))),
% 0.37/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((zip_tseitin_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X2))),
% 0.37/0.62      inference('sup+', [status(thm)], ['7', '16'])).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (![X9 : $i, X11 : $i]:
% 0.37/0.62         (((k4_xboole_0 @ (k1_tarski @ X9) @ X11) = (k1_xboole_0))
% 0.37/0.62          | ~ (r2_hidden @ X9 @ X11))),
% 0.37/0.62      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((zip_tseitin_0 @ (k1_tarski @ X1) @ X2)
% 0.37/0.62          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (![X6 : $i, X7 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X6 @ X7)
% 0.37/0.62          | ((k4_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_tarski @ X6)))),
% 0.37/0.62      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.37/0.62          | (zip_tseitin_0 @ (k1_tarski @ X0) @ X2)
% 0.37/0.62          | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X30 : $i, X31 : $i]:
% 0.37/0.62         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X0 @ X1) | (zip_tseitin_0 @ (k1_tarski @ X0) @ X2))),
% 0.37/0.62      inference('clc', [status(thm)], ['21', '22'])).
% 0.37/0.62  thf('24', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((zip_tseitin_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X2))),
% 0.37/0.62      inference('sup+', [status(thm)], ['7', '16'])).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      (![X0 : $i, X2 : $i]: (zip_tseitin_0 @ (k1_tarski @ X0) @ X2)),
% 0.37/0.62      inference('clc', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('26', plain, ((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.37/0.62      inference('demod', [status(thm)], ['6', '25'])).
% 0.37/0.62  thf('27', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ 
% 0.37/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.62         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.37/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.37/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.37/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.62  thf('30', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['3', '26', '29'])).
% 0.37/0.62  thf(d4_funct_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.62       ( ![B:$i,C:$i]:
% 0.37/0.62         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.37/0.62             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.37/0.62               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.62           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.37/0.62             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.37/0.62               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.37/0.62          | (r2_hidden @ (k4_tarski @ X20 @ X23) @ X21)
% 0.37/0.62          | ((X23) != (k1_funct_1 @ X21 @ X20))
% 0.37/0.62          | ~ (v1_funct_1 @ X21)
% 0.37/0.62          | ~ (v1_relat_1 @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X21)
% 0.37/0.62          | ~ (v1_funct_1 @ X21)
% 0.37/0.62          | (r2_hidden @ (k4_tarski @ X20 @ (k1_funct_1 @ X21 @ X20)) @ X21)
% 0.37/0.62          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X21)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.62          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D)
% 0.37/0.62          | ~ (v1_funct_1 @ sk_D)
% 0.37/0.62          | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.62      inference('sup-', [status(thm)], ['30', '32'])).
% 0.37/0.62  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ 
% 0.37/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(cc1_relset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( v1_relat_1 @ C ) ))).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.62         ((v1_relat_1 @ X24)
% 0.37/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.62  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('38', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.62          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.37/0.62  thf('39', plain,
% 0.37/0.62      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['0', '38'])).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ 
% 0.37/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(l3_subset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X17 @ X18)
% 0.37/0.62          | (r2_hidden @ X17 @ X19)
% 0.37/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.37/0.62  thf('42', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.37/0.62          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.37/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.62  thf('43', plain,
% 0.37/0.62      ((r2_hidden @ (k4_tarski @ sk_C @ (k1_funct_1 @ sk_D @ sk_C)) @ 
% 0.37/0.62        (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['39', '42'])).
% 0.37/0.62  thf(t129_zfmisc_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62     ( ( r2_hidden @
% 0.37/0.62         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.37/0.62       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.37/0.62  thf('44', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.62         (((X14) = (X15))
% 0.37/0.62          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ 
% 0.37/0.62               (k2_zfmisc_1 @ X13 @ (k1_tarski @ X15))))),
% 0.37/0.62      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.37/0.62  thf('45', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.62  thf('46', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('47', plain, ($false),
% 0.37/0.62      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
