%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nHNDh0jHD4

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:49 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 115 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  609 (1421 expanded)
%              Number of equality atoms :   36 (  64 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_D_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D_2 @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['14','23'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X48 @ ( k1_relat_1 @ X49 ) )
      | ( ( k7_partfun1 @ X50 @ X49 @ X48 )
        = ( k1_funct_1 @ X49 @ X48 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v5_relat_1 @ X49 @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v5_relat_1 @ sk_C_2 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( ( k7_partfun1 @ X1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C_2 @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C_2 @ sk_D_2 )
        = ( k1_funct_1 @ sk_C_2 @ sk_D_2 ) )
      | ~ ( v5_relat_1 @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','33'])).

thf('35',plain,
    ( ( k7_partfun1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k1_funct_1 @ sk_C_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['2','34'])).

thf('36',plain,(
    ( k7_partfun1 @ sk_B @ sk_C_2 @ sk_D_2 )
 != ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X53 )
      | ~ ( v1_funct_1 @ X51 )
      | ( v1_xboole_0 @ X52 )
      | ~ ( m1_subset_1 @ X54 @ X52 )
      | ( ( k3_funct_2 @ X52 @ X53 @ X51 @ X54 )
        = ( k1_funct_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k1_funct_1 @ sk_C_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    ( k7_partfun1 @ sk_B @ sk_C_2 @ sk_D_2 )
 != ( k1_funct_1 @ sk_C_2 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nHNDh0jHD4
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:50:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.79/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.79/0.99  % Solved by: fo/fo7.sh
% 0.79/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.99  % done 690 iterations in 0.531s
% 0.79/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.79/0.99  % SZS output start Refutation
% 0.79/0.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.79/0.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.79/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/0.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.79/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/0.99  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.79/0.99  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.79/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/0.99  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.79/0.99  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.79/0.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.79/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.79/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.79/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.99  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.79/0.99  thf(t176_funct_2, conjecture,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.79/0.99       ( ![B:$i]:
% 0.79/0.99         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.79/0.99           ( ![C:$i]:
% 0.79/0.99             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.99                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.99               ( ![D:$i]:
% 0.79/0.99                 ( ( m1_subset_1 @ D @ A ) =>
% 0.79/0.99                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.79/0.99                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.79/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.99    (~( ![A:$i]:
% 0.79/0.99        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.79/0.99          ( ![B:$i]:
% 0.79/0.99            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.79/0.99              ( ![C:$i]:
% 0.79/0.99                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.99                    ( m1_subset_1 @
% 0.79/0.99                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.99                  ( ![D:$i]:
% 0.79/0.99                    ( ( m1_subset_1 @ D @ A ) =>
% 0.79/0.99                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.79/0.99                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.79/0.99    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.79/0.99  thf('0', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(cc2_relset_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/0.99       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.79/0.99  thf('1', plain,
% 0.79/0.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.79/0.99         ((v5_relat_1 @ X31 @ X33)
% 0.79/0.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.79/0.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/0.99  thf('2', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.79/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.79/0.99  thf('3', plain, ((m1_subset_1 @ sk_D_2 @ sk_A)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(d2_subset_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( ( v1_xboole_0 @ A ) =>
% 0.79/0.99         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.79/0.99       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.79/0.99         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.79/0.99  thf('4', plain,
% 0.79/0.99      (![X7 : $i, X8 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X7 @ X8)
% 0.79/0.99          | (r2_hidden @ X7 @ X8)
% 0.79/0.99          | (v1_xboole_0 @ X8))),
% 0.79/0.99      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.79/0.99  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_D_2 @ sk_A))),
% 0.79/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/0.99  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('7', plain, ((r2_hidden @ sk_D_2 @ sk_A)),
% 0.79/0.99      inference('clc', [status(thm)], ['5', '6'])).
% 0.79/0.99  thf('8', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(d1_funct_2, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/0.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.79/0.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.79/0.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.79/0.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.79/0.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.79/0.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.79/0.99  thf(zf_stmt_1, axiom,
% 0.79/0.99    (![C:$i,B:$i,A:$i]:
% 0.79/0.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.79/0.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.79/0.99  thf('9', plain,
% 0.79/0.99      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.79/0.99         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.79/0.99          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.79/0.99          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.79/0.99  thf('10', plain,
% 0.79/0.99      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.79/0.99        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['8', '9'])).
% 0.79/0.99  thf('11', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(redefinition_k1_relset_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/0.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.79/0.99  thf('12', plain,
% 0.79/0.99      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.79/0.99         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.79/0.99          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.79/0.99  thf('13', plain,
% 0.79/0.99      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.79/0.99      inference('sup-', [status(thm)], ['11', '12'])).
% 0.79/0.99  thf('14', plain,
% 0.79/0.99      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.79/0.99        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.79/0.99      inference('demod', [status(thm)], ['10', '13'])).
% 0.79/0.99  thf('15', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.79/0.99  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.79/0.99  thf(zf_stmt_4, axiom,
% 0.79/0.99    (![B:$i,A:$i]:
% 0.79/0.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.79/0.99       ( zip_tseitin_0 @ B @ A ) ))).
% 0.79/0.99  thf(zf_stmt_5, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/0.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.79/0.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.79/0.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.79/0.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.79/0.99  thf('16', plain,
% 0.79/0.99      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.79/0.99         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.79/0.99          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.79/0.99          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.79/0.99  thf('17', plain,
% 0.79/0.99      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.79/0.99        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.79/0.99      inference('sup-', [status(thm)], ['15', '16'])).
% 0.79/0.99  thf('18', plain,
% 0.79/0.99      (![X40 : $i, X41 : $i]:
% 0.79/0.99         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.79/0.99  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.79/0.99  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.79/0.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.79/0.99  thf('20', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.79/0.99      inference('sup+', [status(thm)], ['18', '19'])).
% 0.79/0.99  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('22', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.79/0.99      inference('sup-', [status(thm)], ['20', '21'])).
% 0.79/0.99  thf('23', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 0.79/0.99      inference('demod', [status(thm)], ['17', '22'])).
% 0.79/0.99  thf('24', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.79/0.99      inference('demod', [status(thm)], ['14', '23'])).
% 0.79/0.99  thf(d8_partfun1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.79/0.99       ( ![C:$i]:
% 0.79/0.99         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.79/0.99           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.79/0.99  thf('25', plain,
% 0.79/0.99      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.79/0.99         (~ (r2_hidden @ X48 @ (k1_relat_1 @ X49))
% 0.79/0.99          | ((k7_partfun1 @ X50 @ X49 @ X48) = (k1_funct_1 @ X49 @ X48))
% 0.79/0.99          | ~ (v1_funct_1 @ X49)
% 0.79/0.99          | ~ (v5_relat_1 @ X49 @ X50)
% 0.79/0.99          | ~ (v1_relat_1 @ X49))),
% 0.79/0.99      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.79/0.99  thf('26', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (~ (r2_hidden @ X0 @ sk_A)
% 0.79/0.99          | ~ (v1_relat_1 @ sk_C_2)
% 0.79/0.99          | ~ (v5_relat_1 @ sk_C_2 @ X1)
% 0.79/0.99          | ~ (v1_funct_1 @ sk_C_2)
% 0.79/0.99          | ((k7_partfun1 @ X1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.79/0.99  thf('27', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(cc2_relat_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ A ) =>
% 0.79/0.99       ( ![B:$i]:
% 0.79/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.79/0.99  thf('28', plain,
% 0.79/0.99      (![X10 : $i, X11 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.79/0.99          | (v1_relat_1 @ X10)
% 0.79/0.99          | ~ (v1_relat_1 @ X11))),
% 0.79/0.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/0.99  thf('29', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.79/0.99      inference('sup-', [status(thm)], ['27', '28'])).
% 0.79/0.99  thf(fc6_relat_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.79/0.99  thf('30', plain,
% 0.79/0.99      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.79/0.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/0.99  thf('31', plain, ((v1_relat_1 @ sk_C_2)),
% 0.79/0.99      inference('demod', [status(thm)], ['29', '30'])).
% 0.79/0.99  thf('32', plain, ((v1_funct_1 @ sk_C_2)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('33', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (~ (r2_hidden @ X0 @ sk_A)
% 0.79/0.99          | ~ (v5_relat_1 @ sk_C_2 @ X1)
% 0.79/0.99          | ((k7_partfun1 @ X1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['26', '31', '32'])).
% 0.79/0.99  thf('34', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k7_partfun1 @ X0 @ sk_C_2 @ sk_D_2)
% 0.79/0.99            = (k1_funct_1 @ sk_C_2 @ sk_D_2))
% 0.79/0.99          | ~ (v5_relat_1 @ sk_C_2 @ X0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['7', '33'])).
% 0.79/0.99  thf('35', plain,
% 0.79/0.99      (((k7_partfun1 @ sk_B @ sk_C_2 @ sk_D_2) = (k1_funct_1 @ sk_C_2 @ sk_D_2))),
% 0.79/0.99      inference('sup-', [status(thm)], ['2', '34'])).
% 0.79/0.99  thf('36', plain,
% 0.79/0.99      (((k7_partfun1 @ sk_B @ sk_C_2 @ sk_D_2)
% 0.79/0.99         != (k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('37', plain, ((m1_subset_1 @ sk_D_2 @ sk_A)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('38', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(redefinition_k3_funct_2, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/0.99     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.79/0.99         ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/0.99         ( m1_subset_1 @ D @ A ) ) =>
% 0.79/0.99       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.79/0.99  thf('39', plain,
% 0.79/0.99      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 0.79/0.99          | ~ (v1_funct_2 @ X51 @ X52 @ X53)
% 0.79/0.99          | ~ (v1_funct_1 @ X51)
% 0.79/0.99          | (v1_xboole_0 @ X52)
% 0.79/0.99          | ~ (m1_subset_1 @ X54 @ X52)
% 0.79/0.99          | ((k3_funct_2 @ X52 @ X53 @ X51 @ X54) = (k1_funct_1 @ X51 @ X54)))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.79/0.99  thf('40', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.79/0.99            = (k1_funct_1 @ sk_C_2 @ X0))
% 0.79/0.99          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.79/0.99          | (v1_xboole_0 @ sk_A)
% 0.79/0.99          | ~ (v1_funct_1 @ sk_C_2)
% 0.79/0.99          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 0.79/0.99      inference('sup-', [status(thm)], ['38', '39'])).
% 0.79/0.99  thf('41', plain, ((v1_funct_1 @ sk_C_2)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('42', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('43', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.79/0.99            = (k1_funct_1 @ sk_C_2 @ X0))
% 0.79/0.99          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.79/0.99          | (v1_xboole_0 @ sk_A))),
% 0.79/0.99      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.79/0.99  thf('44', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('45', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.79/0.99          | ((k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0)
% 0.79/0.99              = (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.79/0.99      inference('clc', [status(thm)], ['43', '44'])).
% 0.79/0.99  thf('46', plain,
% 0.79/0.99      (((k3_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D_2)
% 0.79/0.99         = (k1_funct_1 @ sk_C_2 @ sk_D_2))),
% 0.79/0.99      inference('sup-', [status(thm)], ['37', '45'])).
% 0.79/0.99  thf('47', plain,
% 0.79/0.99      (((k7_partfun1 @ sk_B @ sk_C_2 @ sk_D_2)
% 0.79/0.99         != (k1_funct_1 @ sk_C_2 @ sk_D_2))),
% 0.79/0.99      inference('demod', [status(thm)], ['36', '46'])).
% 0.79/0.99  thf('48', plain, ($false),
% 0.79/0.99      inference('simplify_reflect-', [status(thm)], ['35', '47'])).
% 0.79/0.99  
% 0.79/0.99  % SZS output end Refutation
% 0.79/0.99  
% 0.79/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
