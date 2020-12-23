%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CkzrhegLZq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:13 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 105 expanded)
%              Number of leaves         :   44 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  596 ( 907 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( v5_relat_1 @ X52 @ X54 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_funct_2 @ X65 @ X63 @ X64 )
      | ( X63
        = ( k1_relset_1 @ X63 @ X64 @ X65 ) )
      | ~ ( zip_tseitin_2 @ X65 @ X64 @ X63 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_2 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( zip_tseitin_1 @ X66 @ X67 )
      | ( zip_tseitin_2 @ X68 @ X66 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X66 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('10',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X61: $i,X62: $i] :
      ( ( zip_tseitin_1 @ X61 @ X62 )
      | ( X61 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    zip_tseitin_2 @ sk_D_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k1_relset_1 @ X59 @ X60 @ X58 )
        = ( k1_relat_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_2 ) @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','16','19'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k1_relat_1 @ X40 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X40 @ X39 ) @ X41 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v5_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( v1_relat_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D_1 @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C_2 ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('33',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_2 ) @ ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D_1 @ sk_C_2 ) @ sk_B_2 @ sk_B_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ sk_C_2 )
      = sk_B_2 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C_2 )
      = sk_B_2 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C_2 )
    = sk_B_2 ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_2 )
 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CkzrhegLZq
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:18:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 232 iterations in 0.150s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.61  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.42/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.42/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.42/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.61  thf(d1_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.61       ( ![E:$i]:
% 0.42/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.42/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, axiom,
% 0.42/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.42/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.42/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.42/0.61          | ((X5) = (X6))
% 0.42/0.61          | ((X5) = (X7))
% 0.42/0.61          | ((X5) = (X8)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t65_funct_2, conjecture,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.61         ( m1_subset_1 @
% 0.42/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.61       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.42/0.61            ( m1_subset_1 @
% 0.42/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.42/0.61          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(cc2_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.44/0.61         ((v5_relat_1 @ X52 @ X54)
% 0.44/0.61          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.61  thf('3', plain, ((v5_relat_1 @ sk_D_1 @ (k1_tarski @ sk_B_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.61  thf('4', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('5', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_2))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(d1_funct_2, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_2, axiom,
% 0.44/0.61    (![C:$i,B:$i,A:$i]:
% 0.44/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.44/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.44/0.61         (~ (v1_funct_2 @ X65 @ X63 @ X64)
% 0.44/0.61          | ((X63) = (k1_relset_1 @ X63 @ X64 @ X65))
% 0.44/0.61          | ~ (zip_tseitin_2 @ X65 @ X64 @ X63))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.61  thf('7', plain,
% 0.44/0.61      ((~ (zip_tseitin_2 @ sk_D_1 @ (k1_tarski @ sk_B_2) @ sk_A)
% 0.44/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_2) @ sk_D_1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.44/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_5, axiom,
% 0.44/0.61    (![B:$i,A:$i]:
% 0.44/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.44/0.61  thf(zf_stmt_6, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.44/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.44/0.61         (~ (zip_tseitin_1 @ X66 @ X67)
% 0.44/0.61          | (zip_tseitin_2 @ X68 @ X66 @ X67)
% 0.44/0.61          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X66))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      (((zip_tseitin_2 @ sk_D_1 @ (k1_tarski @ sk_B_2) @ sk_A)
% 0.44/0.61        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B_2) @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.61  thf('11', plain,
% 0.44/0.61      (![X61 : $i, X62 : $i]:
% 0.44/0.61         ((zip_tseitin_1 @ X61 @ X62) | ((X61) = (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.61  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 0.44/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.44/0.61  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.44/0.61  thf('14', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X27))),
% 0.44/0.61      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.44/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('16', plain, ((zip_tseitin_2 @ sk_D_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.44/0.61      inference('demod', [status(thm)], ['10', '15'])).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.44/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.44/0.61         (((k1_relset_1 @ X59 @ X60 @ X58) = (k1_relat_1 @ X58))
% 0.44/0.61          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_2) @ sk_D_1)
% 0.44/0.61         = (k1_relat_1 @ sk_D_1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.61  thf('20', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.61      inference('demod', [status(thm)], ['7', '16', '19'])).
% 0.44/0.61  thf(t176_funct_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.61       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.44/0.61         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.44/0.61  thf('21', plain,
% 0.44/0.61      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X39 @ (k1_relat_1 @ X40))
% 0.44/0.61          | (m1_subset_1 @ (k1_funct_1 @ X40 @ X39) @ X41)
% 0.44/0.61          | ~ (v1_funct_1 @ X40)
% 0.44/0.61          | ~ (v5_relat_1 @ X40 @ X41)
% 0.44/0.61          | ~ (v1_relat_1 @ X40))),
% 0.44/0.61      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.44/0.61          | ~ (v1_relat_1 @ sk_D_1)
% 0.44/0.61          | ~ (v5_relat_1 @ sk_D_1 @ X1)
% 0.44/0.61          | ~ (v1_funct_1 @ sk_D_1)
% 0.44/0.61          | (m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_D_1 @ 
% 0.44/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf(cc1_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( v1_relat_1 @ C ) ))).
% 0.44/0.61  thf('24', plain,
% 0.44/0.61      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.44/0.61         ((v1_relat_1 @ X49)
% 0.44/0.61          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.61  thf('25', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf('26', plain, ((v1_funct_1 @ sk_D_1)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.44/0.61          | ~ (v5_relat_1 @ sk_D_1 @ X1)
% 0.44/0.61          | (m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1))),
% 0.44/0.61      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ sk_C_2) @ X0)
% 0.44/0.61          | ~ (v5_relat_1 @ sk_D_1 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['4', '27'])).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      ((m1_subset_1 @ (k1_funct_1 @ sk_D_1 @ sk_C_2) @ (k1_tarski @ sk_B_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['3', '28'])).
% 0.44/0.61  thf(t2_subset, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.44/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.44/0.61  thf('30', plain,
% 0.44/0.61      (![X33 : $i, X34 : $i]:
% 0.44/0.61         ((r2_hidden @ X33 @ X34)
% 0.44/0.61          | (v1_xboole_0 @ X34)
% 0.44/0.61          | ~ (m1_subset_1 @ X33 @ X34))),
% 0.44/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.44/0.61        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_2) @ (k1_tarski @ sk_B_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.61  thf('32', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X27))),
% 0.44/0.61      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_2) @ (k1_tarski @ sk_B_2))),
% 0.44/0.61      inference('clc', [status(thm)], ['31', '32'])).
% 0.44/0.61  thf(t69_enumset1, axiom,
% 0.44/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.44/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.61  thf(t70_enumset1, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (![X17 : $i, X18 : $i]:
% 0.44/0.61         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.61  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_8, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.61       ( ![E:$i]:
% 0.44/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X14 @ X13)
% 0.44/0.61          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.44/0.61          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.44/0.61  thf('37', plain,
% 0.44/0.61      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.44/0.61         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.44/0.61          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.61  thf('38', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['35', '37'])).
% 0.44/0.61  thf('39', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.44/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['34', '38'])).
% 0.44/0.61  thf('40', plain,
% 0.44/0.61      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D_1 @ sk_C_2) @ sk_B_2 @ sk_B_2 @ 
% 0.44/0.61          sk_B_2)),
% 0.44/0.61      inference('sup-', [status(thm)], ['33', '39'])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      ((((k1_funct_1 @ sk_D_1 @ sk_C_2) = (sk_B_2))
% 0.44/0.61        | ((k1_funct_1 @ sk_D_1 @ sk_C_2) = (sk_B_2))
% 0.44/0.61        | ((k1_funct_1 @ sk_D_1 @ sk_C_2) = (sk_B_2)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['0', '40'])).
% 0.44/0.61  thf('42', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_2) = (sk_B_2))),
% 0.44/0.61      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.61  thf('43', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_2) != (sk_B_2))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('44', plain, ($false),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
