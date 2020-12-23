%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f2F6vn0rKU

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:49 EST 2020

% Result     : Theorem 9.02s
% Output     : Refutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 119 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  605 (1419 expanded)
%              Number of equality atoms :   39 (  67 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
    | ( r2_hidden @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_A_1 ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1 ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('19',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('20',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,
    ( sk_A_1
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','27'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('29',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ ( k1_relat_1 @ X46 ) )
      | ( ( k7_partfun1 @ X47 @ X46 @ X45 )
        = ( k1_funct_1 @ X46 @ X45 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v5_relat_1 @ X46 @ X47 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A_1 )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,
    ( ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','36'])).

thf('38',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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

thf('41',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( v1_funct_1 @ X48 )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X51 @ X49 )
      | ( ( k3_funct_2 @ X49 @ X50 @ X48 @ X51 )
        = ( k1_funct_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['38','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.f2F6vn0rKU
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:31:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 9.02/9.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.02/9.23  % Solved by: fo/fo7.sh
% 9.02/9.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.02/9.23  % done 9949 iterations in 8.776s
% 9.02/9.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.02/9.23  % SZS output start Refutation
% 9.02/9.23  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 9.02/9.23  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.02/9.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 9.02/9.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.02/9.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.02/9.23  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 9.02/9.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.02/9.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.02/9.23  thf(sk_A_type, type, sk_A: $i).
% 9.02/9.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.02/9.23  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 9.02/9.23  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.02/9.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.02/9.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.02/9.23  thf(sk_C_type, type, sk_C: $i).
% 9.02/9.23  thf(sk_D_type, type, sk_D: $i).
% 9.02/9.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.02/9.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 9.02/9.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.02/9.23  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.02/9.23  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 9.02/9.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.02/9.23  thf(sk_A_1_type, type, sk_A_1: $i).
% 9.02/9.23  thf(t176_funct_2, conjecture,
% 9.02/9.23    (![A:$i]:
% 9.02/9.23     ( ( ~( v1_xboole_0 @ A ) ) =>
% 9.02/9.23       ( ![B:$i]:
% 9.02/9.23         ( ( ~( v1_xboole_0 @ B ) ) =>
% 9.02/9.23           ( ![C:$i]:
% 9.02/9.23             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.02/9.23                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.02/9.23               ( ![D:$i]:
% 9.02/9.23                 ( ( m1_subset_1 @ D @ A ) =>
% 9.02/9.23                   ( ( k7_partfun1 @ B @ C @ D ) =
% 9.02/9.23                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 9.02/9.23  thf(zf_stmt_0, negated_conjecture,
% 9.02/9.23    (~( ![A:$i]:
% 9.02/9.23        ( ( ~( v1_xboole_0 @ A ) ) =>
% 9.02/9.23          ( ![B:$i]:
% 9.02/9.23            ( ( ~( v1_xboole_0 @ B ) ) =>
% 9.02/9.23              ( ![C:$i]:
% 9.02/9.23                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.02/9.23                    ( m1_subset_1 @
% 9.02/9.23                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.02/9.23                  ( ![D:$i]:
% 9.02/9.23                    ( ( m1_subset_1 @ D @ A ) =>
% 9.02/9.23                      ( ( k7_partfun1 @ B @ C @ D ) =
% 9.02/9.23                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 9.02/9.23    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 9.02/9.23  thf('0', plain,
% 9.02/9.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf(cc2_relset_1, axiom,
% 9.02/9.23    (![A:$i,B:$i,C:$i]:
% 9.02/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.02/9.23       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 9.02/9.23  thf('1', plain,
% 9.02/9.23      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.02/9.23         ((v5_relat_1 @ X28 @ X30)
% 9.02/9.23          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 9.02/9.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.02/9.23  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 9.02/9.23      inference('sup-', [status(thm)], ['0', '1'])).
% 9.02/9.23  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A_1)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf(t2_subset, axiom,
% 9.02/9.23    (![A:$i,B:$i]:
% 9.02/9.23     ( ( m1_subset_1 @ A @ B ) =>
% 9.02/9.23       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 9.02/9.23  thf('4', plain,
% 9.02/9.23      (![X10 : $i, X11 : $i]:
% 9.02/9.23         ((r2_hidden @ X10 @ X11)
% 9.02/9.23          | (v1_xboole_0 @ X11)
% 9.02/9.23          | ~ (m1_subset_1 @ X10 @ X11))),
% 9.02/9.23      inference('cnf', [status(esa)], [t2_subset])).
% 9.02/9.23  thf('5', plain, (((v1_xboole_0 @ sk_A_1) | (r2_hidden @ sk_D @ sk_A_1))),
% 9.02/9.23      inference('sup-', [status(thm)], ['3', '4'])).
% 9.02/9.23  thf('6', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf('7', plain, ((r2_hidden @ sk_D @ sk_A_1)),
% 9.02/9.23      inference('clc', [status(thm)], ['5', '6'])).
% 9.02/9.23  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf(d1_funct_2, axiom,
% 9.02/9.23    (![A:$i,B:$i,C:$i]:
% 9.02/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.02/9.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.02/9.23           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 9.02/9.23             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 9.02/9.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.02/9.23           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 9.02/9.23             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 9.02/9.23  thf(zf_stmt_1, axiom,
% 9.02/9.23    (![C:$i,B:$i,A:$i]:
% 9.02/9.23     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 9.02/9.23       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 9.02/9.23  thf('9', plain,
% 9.02/9.23      (![X39 : $i, X40 : $i, X41 : $i]:
% 9.02/9.23         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 9.02/9.23          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 9.02/9.23          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.02/9.23  thf('10', plain,
% 9.02/9.23      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)
% 9.02/9.23        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C)))),
% 9.02/9.23      inference('sup-', [status(thm)], ['8', '9'])).
% 9.02/9.23  thf('11', plain,
% 9.02/9.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf(redefinition_k1_relset_1, axiom,
% 9.02/9.23    (![A:$i,B:$i,C:$i]:
% 9.02/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.02/9.23       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 9.02/9.23  thf('12', plain,
% 9.02/9.23      (![X31 : $i, X32 : $i, X33 : $i]:
% 9.02/9.23         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 9.02/9.23          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 9.02/9.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.02/9.23  thf('13', plain,
% 9.02/9.23      (((k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 9.02/9.23      inference('sup-', [status(thm)], ['11', '12'])).
% 9.02/9.23  thf('14', plain,
% 9.02/9.23      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)
% 9.02/9.23        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 9.02/9.23      inference('demod', [status(thm)], ['10', '13'])).
% 9.02/9.23  thf('15', plain,
% 9.02/9.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 9.02/9.23  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 9.02/9.23  thf(zf_stmt_4, axiom,
% 9.02/9.23    (![B:$i,A:$i]:
% 9.02/9.23     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.02/9.23       ( zip_tseitin_0 @ B @ A ) ))).
% 9.02/9.23  thf(zf_stmt_5, axiom,
% 9.02/9.23    (![A:$i,B:$i,C:$i]:
% 9.02/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.02/9.23       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 9.02/9.23         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.02/9.23           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 9.02/9.23             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 9.02/9.23  thf('16', plain,
% 9.02/9.23      (![X42 : $i, X43 : $i, X44 : $i]:
% 9.02/9.23         (~ (zip_tseitin_0 @ X42 @ X43)
% 9.02/9.23          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 9.02/9.23          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.02/9.23  thf('17', plain,
% 9.02/9.23      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)
% 9.02/9.23        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A_1))),
% 9.02/9.23      inference('sup-', [status(thm)], ['15', '16'])).
% 9.02/9.23  thf('18', plain,
% 9.02/9.23      (![X37 : $i, X38 : $i]:
% 9.02/9.23         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_4])).
% 9.02/9.23  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 9.02/9.23  thf('19', plain, ((v1_xboole_0 @ sk_A)),
% 9.02/9.23      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 9.02/9.23  thf('20', plain, ((v1_xboole_0 @ sk_A)),
% 9.02/9.23      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 9.02/9.23  thf(l13_xboole_0, axiom,
% 9.02/9.23    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 9.02/9.23  thf('21', plain,
% 9.02/9.23      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 9.02/9.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 9.02/9.23  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 9.02/9.23      inference('sup-', [status(thm)], ['20', '21'])).
% 9.02/9.23  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.02/9.23      inference('demod', [status(thm)], ['19', '22'])).
% 9.02/9.23  thf('24', plain,
% 9.02/9.23      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 9.02/9.23      inference('sup+', [status(thm)], ['18', '23'])).
% 9.02/9.23  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf('26', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 9.02/9.23      inference('sup-', [status(thm)], ['24', '25'])).
% 9.02/9.23  thf('27', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)),
% 9.02/9.23      inference('demod', [status(thm)], ['17', '26'])).
% 9.02/9.23  thf('28', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 9.02/9.23      inference('demod', [status(thm)], ['14', '27'])).
% 9.02/9.23  thf(d8_partfun1, axiom,
% 9.02/9.23    (![A:$i,B:$i]:
% 9.02/9.23     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 9.02/9.23       ( ![C:$i]:
% 9.02/9.23         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 9.02/9.23           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 9.02/9.23  thf('29', plain,
% 9.02/9.23      (![X45 : $i, X46 : $i, X47 : $i]:
% 9.02/9.23         (~ (r2_hidden @ X45 @ (k1_relat_1 @ X46))
% 9.02/9.23          | ((k7_partfun1 @ X47 @ X46 @ X45) = (k1_funct_1 @ X46 @ X45))
% 9.02/9.23          | ~ (v1_funct_1 @ X46)
% 9.02/9.23          | ~ (v5_relat_1 @ X46 @ X47)
% 9.02/9.23          | ~ (v1_relat_1 @ X46))),
% 9.02/9.23      inference('cnf', [status(esa)], [d8_partfun1])).
% 9.02/9.23  thf('30', plain,
% 9.02/9.23      (![X0 : $i, X1 : $i]:
% 9.02/9.23         (~ (r2_hidden @ X0 @ sk_A_1)
% 9.02/9.23          | ~ (v1_relat_1 @ sk_C)
% 9.02/9.23          | ~ (v5_relat_1 @ sk_C @ X1)
% 9.02/9.23          | ~ (v1_funct_1 @ sk_C)
% 9.02/9.23          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 9.02/9.23      inference('sup-', [status(thm)], ['28', '29'])).
% 9.02/9.23  thf('31', plain,
% 9.02/9.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf(cc1_relset_1, axiom,
% 9.02/9.23    (![A:$i,B:$i,C:$i]:
% 9.02/9.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.02/9.23       ( v1_relat_1 @ C ) ))).
% 9.02/9.23  thf('32', plain,
% 9.02/9.23      (![X25 : $i, X26 : $i, X27 : $i]:
% 9.02/9.23         ((v1_relat_1 @ X25)
% 9.02/9.23          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 9.02/9.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 9.02/9.23  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 9.02/9.23      inference('sup-', [status(thm)], ['31', '32'])).
% 9.02/9.23  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf('35', plain,
% 9.02/9.23      (![X0 : $i, X1 : $i]:
% 9.02/9.23         (~ (r2_hidden @ X0 @ sk_A_1)
% 9.02/9.23          | ~ (v5_relat_1 @ sk_C @ X1)
% 9.02/9.23          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 9.02/9.23      inference('demod', [status(thm)], ['30', '33', '34'])).
% 9.02/9.23  thf('36', plain,
% 9.02/9.23      (![X0 : $i]:
% 9.02/9.23         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 9.02/9.23          | ~ (v5_relat_1 @ sk_C @ X0))),
% 9.02/9.23      inference('sup-', [status(thm)], ['7', '35'])).
% 9.02/9.23  thf('37', plain,
% 9.02/9.23      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 9.02/9.23      inference('sup-', [status(thm)], ['2', '36'])).
% 9.02/9.23  thf('38', plain,
% 9.02/9.23      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D)
% 9.02/9.23         != (k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf('39', plain, ((m1_subset_1 @ sk_D @ sk_A_1)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf('40', plain,
% 9.02/9.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf(redefinition_k3_funct_2, axiom,
% 9.02/9.23    (![A:$i,B:$i,C:$i,D:$i]:
% 9.02/9.23     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 9.02/9.23         ( v1_funct_2 @ C @ A @ B ) & 
% 9.02/9.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.02/9.23         ( m1_subset_1 @ D @ A ) ) =>
% 9.02/9.23       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 9.02/9.23  thf('41', plain,
% 9.02/9.23      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 9.02/9.23         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 9.02/9.23          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 9.02/9.23          | ~ (v1_funct_1 @ X48)
% 9.02/9.23          | (v1_xboole_0 @ X49)
% 9.02/9.23          | ~ (m1_subset_1 @ X51 @ X49)
% 9.02/9.23          | ((k3_funct_2 @ X49 @ X50 @ X48 @ X51) = (k1_funct_1 @ X48 @ X51)))),
% 9.02/9.23      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 9.02/9.23  thf('42', plain,
% 9.02/9.23      (![X0 : $i]:
% 9.02/9.23         (((k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0)
% 9.02/9.23            = (k1_funct_1 @ sk_C @ X0))
% 9.02/9.23          | ~ (m1_subset_1 @ X0 @ sk_A_1)
% 9.02/9.23          | (v1_xboole_0 @ sk_A_1)
% 9.02/9.23          | ~ (v1_funct_1 @ sk_C)
% 9.02/9.23          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1))),
% 9.02/9.23      inference('sup-', [status(thm)], ['40', '41'])).
% 9.02/9.23  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf('44', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf('45', plain,
% 9.02/9.23      (![X0 : $i]:
% 9.02/9.23         (((k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0)
% 9.02/9.23            = (k1_funct_1 @ sk_C @ X0))
% 9.02/9.23          | ~ (m1_subset_1 @ X0 @ sk_A_1)
% 9.02/9.23          | (v1_xboole_0 @ sk_A_1))),
% 9.02/9.23      inference('demod', [status(thm)], ['42', '43', '44'])).
% 9.02/9.23  thf('46', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 9.02/9.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.02/9.23  thf('47', plain,
% 9.02/9.23      (![X0 : $i]:
% 9.02/9.23         (~ (m1_subset_1 @ X0 @ sk_A_1)
% 9.02/9.23          | ((k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0)
% 9.02/9.23              = (k1_funct_1 @ sk_C @ X0)))),
% 9.02/9.23      inference('clc', [status(thm)], ['45', '46'])).
% 9.02/9.23  thf('48', plain,
% 9.02/9.23      (((k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)
% 9.02/9.23         = (k1_funct_1 @ sk_C @ sk_D))),
% 9.02/9.23      inference('sup-', [status(thm)], ['39', '47'])).
% 9.02/9.23  thf('49', plain,
% 9.02/9.23      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 9.02/9.23      inference('demod', [status(thm)], ['38', '48'])).
% 9.02/9.23  thf('50', plain, ($false),
% 9.02/9.23      inference('simplify_reflect-', [status(thm)], ['37', '49'])).
% 9.02/9.23  
% 9.02/9.23  % SZS output end Refutation
% 9.02/9.23  
% 9.02/9.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
