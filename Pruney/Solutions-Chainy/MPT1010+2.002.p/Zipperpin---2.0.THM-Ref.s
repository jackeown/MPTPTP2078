%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NbeRdgekMq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 108 expanded)
%              Number of leaves         :   43 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  567 ( 942 expanded)
%              Number of equality atoms :   45 (  61 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( v5_relat_1 @ X52 @ X54 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_2 @ X62 @ X60 @ X61 )
      | ( X60
        = ( k1_relset_1 @ X60 @ X61 @ X62 ) )
      | ~ ( zip_tseitin_1 @ X62 @ X61 @ X60 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X58: $i,X59: $i] :
      ( ( zip_tseitin_0 @ X58 @ X59 )
      | ( X58 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('9',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( zip_tseitin_0 @ X63 @ X64 )
      | ( zip_tseitin_1 @ X65 @ X63 @ X64 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X42 != X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X41 ) )
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X41: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X41 ) @ ( k1_tarski @ X41 ) )
     != ( k1_tarski @ X41 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ! [X41: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X41 ) ) ),
    inference(demod,[status(thm)],['13','19','20'])).

thf('22',plain,(
    zip_tseitin_1 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['11','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( ( k1_relset_1 @ X56 @ X57 @ X55 )
        = ( k1_relat_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','22','25'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('27',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X47 @ ( k1_relat_1 @ X48 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X48 @ X47 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( v1_relat_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','33'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k2_relat_1 @ X45 ) )
      | ( r2_hidden @ X44 @ X46 )
      | ~ ( v5_relat_1 @ X45 @ X46 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['29','30'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NbeRdgekMq
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 80 iterations in 0.024s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(t65_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.46         ( m1_subset_1 @
% 0.20/0.46           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.46       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.46            ( m1_subset_1 @
% 0.20/0.46              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.46          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc2_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.20/0.46         ((v5_relat_1 @ X52 @ X54)
% 0.20/0.46          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.46  thf('2', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d1_funct_2, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_1, axiom,
% 0.20/0.46    (![C:$i,B:$i,A:$i]:
% 0.20/0.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.20/0.46         (~ (v1_funct_2 @ X62 @ X60 @ X61)
% 0.20/0.46          | ((X60) = (k1_relset_1 @ X60 @ X61 @ X62))
% 0.20/0.46          | ~ (zip_tseitin_1 @ X62 @ X61 @ X60))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((~ (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.46        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(zf_stmt_2, axiom,
% 0.20/0.46    (![B:$i,A:$i]:
% 0.20/0.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.46       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X58 : $i, X59 : $i]:
% 0.20/0.46         ((zip_tseitin_0 @ X58 @ X59) | ((X58) = (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.46  thf(zf_stmt_5, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.20/0.46         (~ (zip_tseitin_0 @ X63 @ X64)
% 0.20/0.46          | (zip_tseitin_1 @ X65 @ X63 @ X64)
% 0.20/0.46          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X63))))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.46        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.46        | (zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.46  thf(t20_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46         ( k1_tarski @ A ) ) <=>
% 0.20/0.46       ( ( A ) != ( B ) ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X41 : $i, X42 : $i]:
% 0.20/0.46         (((X42) != (X41))
% 0.20/0.46          | ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X41))
% 0.20/0.46              != (k1_tarski @ X42)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X41 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ (k1_tarski @ X41) @ (k1_tarski @ X41))
% 0.20/0.46           != (k1_tarski @ X41))),
% 0.20/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.46  thf(d10_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.46  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.46      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.46  thf(t28_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]:
% 0.20/0.46         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.46  thf('17', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf(t100_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.46           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf(t92_xboole_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('20', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.46  thf('21', plain, (![X41 : $i]: ((k1_xboole_0) != (k1_tarski @ X41))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '19', '20'])).
% 0.20/0.46  thf('22', plain, ((zip_tseitin_1 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.20/0.46      inference('clc', [status(thm)], ['11', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.20/0.46         (((k1_relset_1 @ X56 @ X57 @ X55) = (k1_relat_1 @ X55))
% 0.20/0.46          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.46      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.46  thf('26', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '22', '25'])).
% 0.20/0.46  thf(t12_funct_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.46         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X47 : $i, X48 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X47 @ (k1_relat_1 @ X48))
% 0.20/0.46          | (r2_hidden @ (k1_funct_1 @ X48 @ X47) @ (k2_relat_1 @ X48))
% 0.20/0.46          | ~ (v1_funct_1 @ X48)
% 0.20/0.46          | ~ (v1_relat_1 @ X48))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.46          | ~ (v1_relat_1 @ sk_D)
% 0.20/0.46          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.46          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc1_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( v1_relat_1 @ C ) ))).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.46         ((v1_relat_1 @ X49)
% 0.20/0.46          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.46  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.46          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.46      inference('demod', [status(thm)], ['28', '31', '32'])).
% 0.20/0.46  thf('34', plain,
% 0.20/0.46      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '33'])).
% 0.20/0.46  thf(t202_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X44 @ (k2_relat_1 @ X45))
% 0.20/0.46          | (r2_hidden @ X44 @ X46)
% 0.20/0.46          | ~ (v5_relat_1 @ X45 @ X46)
% 0.20/0.46          | ~ (v1_relat_1 @ X45))),
% 0.20/0.46      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ sk_D)
% 0.20/0.46          | ~ (v5_relat_1 @ sk_D @ X0)
% 0.20/0.46          | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.46  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('38', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v5_relat_1 @ sk_D @ X0)
% 0.20/0.46          | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '38'])).
% 0.20/0.46  thf(d1_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.46  thf('40', plain,
% 0.20/0.46      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X11 @ X10)
% 0.20/0.46          | ((X11) = (X8))
% 0.20/0.46          | ((X10) != (k1_tarski @ X8)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.46  thf('41', plain,
% 0.20/0.46      (![X8 : $i, X11 : $i]:
% 0.20/0.46         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.46  thf('42', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.46  thf('43', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('44', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
