%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dW9XHVJxDw

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:49 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 114 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  602 (1414 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t176_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( k7_partfun1 @ B @ C @ D )
                      = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X54 )
      | ~ ( v1_funct_1 @ X52 )
      | ( v1_xboole_0 @ X53 )
      | ~ ( m1_subset_1 @ X55 @ X53 )
      | ( ( k3_funct_2 @ X53 @ X54 @ X52 @ X55 )
        = ( k1_funct_1 @ X52 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D )
    = ( k1_funct_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ( k7_partfun1 @ sk_B @ sk_C_2 @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v5_relat_1 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
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

thf('20',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('23',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['21','30','33'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('35',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X49 @ ( k1_relat_1 @ X50 ) )
      | ( ( k7_partfun1 @ X51 @ X50 @ X49 )
        = ( k1_funct_1 @ X50 @ X49 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v5_relat_1 @ X50 @ X51 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v5_relat_1 @ sk_C_2 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( ( k7_partfun1 @ X1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C_2 @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C_2 @ sk_D )
        = ( k1_funct_1 @ sk_C_2 @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','43'])).

thf('45',plain,
    ( ( k7_partfun1 @ sk_B @ sk_C_2 @ sk_D )
    = ( k1_funct_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','44'])).

thf('46',plain,(
    ( k1_funct_1 @ sk_C_2 @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['10','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dW9XHVJxDw
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 177 iterations in 0.097s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.37/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.54  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.37/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.54  thf(t176_funct_2, conjecture,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.54           ( ![C:$i]:
% 0.37/0.54             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.54                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.54               ( ![D:$i]:
% 0.37/0.54                 ( ( m1_subset_1 @ D @ A ) =>
% 0.37/0.54                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.37/0.54                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i]:
% 0.37/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.54          ( ![B:$i]:
% 0.37/0.54            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.54              ( ![C:$i]:
% 0.37/0.54                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.54                    ( m1_subset_1 @
% 0.37/0.54                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.54                  ( ![D:$i]:
% 0.37/0.54                    ( ( m1_subset_1 @ D @ A ) =>
% 0.37/0.54                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.37/0.54                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.37/0.54  thf('0', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(redefinition_k3_funct_2, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.37/0.54         ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.54         ( m1_subset_1 @ D @ A ) ) =>
% 0.37/0.54       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 0.37/0.54          | ~ (v1_funct_2 @ X52 @ X53 @ X54)
% 0.37/0.54          | ~ (v1_funct_1 @ X52)
% 0.37/0.54          | (v1_xboole_0 @ X53)
% 0.37/0.54          | ~ (m1_subset_1 @ X55 @ X53)
% 0.37/0.54          | ((k3_funct_2 @ X53 @ X54 @ X52 @ X55) = (k1_funct_1 @ X52 @ X55)))),
% 0.37/0.54      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.37/0.54            = (k1_funct_1 @ sk_C_2 @ X0))
% 0.37/0.54          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.37/0.54          | (v1_xboole_0 @ sk_A)
% 0.37/0.54          | ~ (v1_funct_1 @ sk_C_2)
% 0.37/0.54          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.54  thf('4', plain, ((v1_funct_1 @ sk_C_2)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('5', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.37/0.54            = (k1_funct_1 @ sk_C_2 @ X0))
% 0.37/0.54          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.37/0.54          | (v1_xboole_0 @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.37/0.54  thf('7', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.37/0.54          | ((k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.37/0.54              = (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.37/0.54      inference('clc', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (((k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)
% 0.37/0.54         = (k1_funct_1 @ sk_C_2 @ sk_D))),
% 0.37/0.54      inference('sup-', [status(thm)], ['0', '8'])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (((k7_partfun1 @ sk_B @ sk_C_2 @ sk_D)
% 0.37/0.54         != (k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(cc2_relset_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.54         ((v5_relat_1 @ X32 @ X34)
% 0.37/0.54          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.54  thf('13', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('14', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(d2_subset_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.37/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.37/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X11 : $i, X12 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X11 @ X12)
% 0.37/0.54          | (r2_hidden @ X11 @ X12)
% 0.37/0.54          | (v1_xboole_0 @ X12))),
% 0.37/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.54  thf('16', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_D @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.54  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('18', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.37/0.54      inference('clc', [status(thm)], ['16', '17'])).
% 0.37/0.54  thf('19', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(d1_funct_2, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_1, axiom,
% 0.37/0.54    (![C:$i,B:$i,A:$i]:
% 0.37/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.54  thf('20', plain,
% 0.37/0.55      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.55         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.37/0.55          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.37/0.55          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.37/0.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.55  thf(zf_stmt_4, axiom,
% 0.37/0.55    (![B:$i,A:$i]:
% 0.37/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.55  thf(zf_stmt_5, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.37/0.55         (~ (zip_tseitin_0 @ X46 @ X47)
% 0.37/0.55          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 0.37/0.55          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.37/0.55        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X41 : $i, X42 : $i]:
% 0.37/0.55         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.37/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.55  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.55  thf('28', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('29', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('30', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 0.37/0.55      inference('demod', [status(thm)], ['24', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.55         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.37/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.55  thf('34', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.37/0.55      inference('demod', [status(thm)], ['21', '30', '33'])).
% 0.37/0.55  thf(d8_partfun1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.55           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X49 @ (k1_relat_1 @ X50))
% 0.37/0.55          | ((k7_partfun1 @ X51 @ X50 @ X49) = (k1_funct_1 @ X50 @ X49))
% 0.37/0.55          | ~ (v1_funct_1 @ X50)
% 0.37/0.55          | ~ (v5_relat_1 @ X50 @ X51)
% 0.37/0.55          | ~ (v1_relat_1 @ X50))),
% 0.37/0.55      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.55          | ~ (v1_relat_1 @ sk_C_2)
% 0.37/0.55          | ~ (v5_relat_1 @ sk_C_2 @ X1)
% 0.37/0.55          | ~ (v1_funct_1 @ sk_C_2)
% 0.37/0.55          | ((k7_partfun1 @ X1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc2_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.37/0.55          | (v1_relat_1 @ X15)
% 0.37/0.55          | ~ (v1_relat_1 @ X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.55  thf(fc6_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.55  thf('41', plain, ((v1_relat_1 @ sk_C_2)),
% 0.37/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain, ((v1_funct_1 @ sk_C_2)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.55          | ~ (v5_relat_1 @ sk_C_2 @ X1)
% 0.37/0.55          | ((k7_partfun1 @ X1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['36', '41', '42'])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k7_partfun1 @ X0 @ sk_C_2 @ sk_D) = (k1_funct_1 @ sk_C_2 @ sk_D))
% 0.37/0.55          | ~ (v5_relat_1 @ sk_C_2 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '43'])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (((k7_partfun1 @ sk_B @ sk_C_2 @ sk_D) = (k1_funct_1 @ sk_C_2 @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (((k1_funct_1 @ sk_C_2 @ sk_D)
% 0.37/0.55         != (k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '45'])).
% 0.37/0.55  thf('47', plain, ($false),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['9', '46'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
