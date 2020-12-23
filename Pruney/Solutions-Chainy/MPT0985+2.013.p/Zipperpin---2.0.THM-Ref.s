%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9sgV0gK90N

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:29 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  202 (1336 expanded)
%              Number of leaves         :   50 ( 419 expanded)
%              Depth                    :   23
%              Number of atoms          : 1320 (19932 expanded)
%              Number of equality atoms :   82 ( 780 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_funct_1 @ X28 )
        = ( k4_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ X0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('30',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['35','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X49: $i] :
      ( ( v1_funct_2 @ X49 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('50',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('52',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('59',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('71',plain,(
    ! [X29: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('72',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('74',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','63','69','75'])).

thf('77',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('78',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('79',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('81',plain,(
    ! [X29: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('83',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('94',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('97',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf('99',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('101',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X25 ) )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('102',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('103',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('106',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B_1 @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['35','46'])).

thf('112',plain,
    ( ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('114',plain,
    ( ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('116',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('117',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','118'])).

thf('120',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('121',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['86','119','120'])).

thf('122',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['79','121'])).

thf('123',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','122'])).

thf('124',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf('126',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['27','123','124','125'])).

thf('127',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('128',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf('130',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X25 ) )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('131',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','122'])).

thf('135',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf('136',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ X0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','128','133','134','135'])).

thf('137',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['86','119','120'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ k1_xboole_0 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('140',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('141',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X51 )
      | ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ X51 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('143',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('144',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('145',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('146',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['138','148'])).

thf('150',plain,(
    $false ),
    inference('sup-',[status(thm)],['5','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9sgV0gK90N
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:47:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 563 iterations in 0.422s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.68/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.68/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.68/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.68/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.68/0.88  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.68/0.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.68/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.68/0.88  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.68/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.88  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.68/0.88  thf(d1_xboole_0, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.68/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.88  thf(t113_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.68/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      (![X6 : $i, X7 : $i]:
% 0.68/0.88         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['1'])).
% 0.68/0.88  thf(t152_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.68/0.88      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.68/0.88  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.68/0.88  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '4'])).
% 0.68/0.88  thf(l13_xboole_0, axiom,
% 0.68/0.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['6', '7'])).
% 0.68/0.88  thf(t31_funct_2, conjecture,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.88       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.68/0.88         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.68/0.88           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.68/0.88           ( m1_subset_1 @
% 0.68/0.88             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.88        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.88            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.68/0.88          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.68/0.88            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.68/0.88              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.68/0.88              ( m1_subset_1 @
% 0.68/0.88                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.68/0.88        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 0.68/0.88        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 0.68/0.88         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('split', [status(esa)], ['9'])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      ((![X0 : $i]:
% 0.68/0.88          (~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_A)
% 0.68/0.88           | ~ (v1_xboole_0 @ X0)
% 0.68/0.88           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.68/0.88         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['8', '10'])).
% 0.68/0.88  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(d9_funct_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.88       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X28 : $i]:
% 0.68/0.88         (~ (v2_funct_1 @ X28)
% 0.68/0.88          | ((k2_funct_1 @ X28) = (k4_relat_1 @ X28))
% 0.68/0.88          | ~ (v1_funct_1 @ X28)
% 0.68/0.88          | ~ (v1_relat_1 @ X28))),
% 0.68/0.88      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_C_1)
% 0.68/0.88        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 0.68/0.88        | ~ (v2_funct_1 @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(cc1_relset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( v1_relat_1 @ C ) ))).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.68/0.88         ((v1_relat_1 @ X32)
% 0.68/0.88          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.68/0.88      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.68/0.88  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.88  thf('18', plain, ((v2_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('19', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      ((![X0 : $i]:
% 0.68/0.88          (~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ X0 @ sk_A)
% 0.68/0.88           | ~ (v1_xboole_0 @ X0)
% 0.68/0.88           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.68/0.88         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['11', '19'])).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.68/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(l3_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X10 @ X11)
% 0.68/0.88          | (r2_hidden @ X10 @ X12)
% 0.68/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.68/0.88      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.68/0.88          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (((v1_xboole_0 @ sk_C_1)
% 0.68/0.88        | (r2_hidden @ (sk_B @ sk_C_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['21', '24'])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (((v1_xboole_0 @ sk_C_1)
% 0.68/0.88        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.88  thf(d1_funct_2, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.68/0.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.68/0.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.68/0.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_1, axiom,
% 0.68/0.88    (![B:$i,A:$i]:
% 0.68/0.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.68/0.88       ( zip_tseitin_0 @ B @ A ) ))).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X41 : $i, X42 : $i]:
% 0.68/0.88         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.68/0.88  thf(zf_stmt_3, axiom,
% 0.68/0.88    (![C:$i,B:$i,A:$i]:
% 0.68/0.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.68/0.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.68/0.88  thf(zf_stmt_5, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.68/0.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.68/0.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.68/0.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.68/0.88         (~ (zip_tseitin_0 @ X46 @ X47)
% 0.68/0.88          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 0.68/0.88          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['28', '31'])).
% 0.68/0.88  thf('33', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.68/0.88         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.68/0.88          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.68/0.88          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.68/0.88  thf('36', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.68/0.88         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.68/0.88          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.88  thf('39', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.68/0.88  thf(t55_funct_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.88       ( ( v2_funct_1 @ A ) =>
% 0.68/0.88         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.68/0.88           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X30 : $i]:
% 0.68/0.88         (~ (v2_funct_1 @ X30)
% 0.68/0.88          | ((k1_relat_1 @ X30) = (k2_relat_1 @ (k2_funct_1 @ X30)))
% 0.68/0.88          | ~ (v1_funct_1 @ X30)
% 0.68/0.88          | ~ (v1_relat_1 @ X30))),
% 0.68/0.88      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.68/0.88        | ~ (v1_relat_1 @ sk_C_1)
% 0.68/0.88        | ~ (v1_funct_1 @ sk_C_1)
% 0.68/0.88        | ~ (v2_funct_1 @ sk_C_1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['39', '40'])).
% 0.68/0.88  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.88  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('44', plain, ((v2_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.68/0.88         = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['38', '45'])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))),
% 0.68/0.88      inference('demod', [status(thm)], ['35', '46'])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      ((((sk_B_1) = (k1_xboole_0))
% 0.68/0.88        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['32', '47'])).
% 0.68/0.88  thf(t3_funct_2, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.88       ( ( v1_funct_1 @ A ) & 
% 0.68/0.88         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.68/0.88         ( m1_subset_1 @
% 0.68/0.88           A @ 
% 0.68/0.88           ( k1_zfmisc_1 @
% 0.68/0.88             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X49 : $i]:
% 0.68/0.88         ((v1_funct_2 @ X49 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))
% 0.68/0.88          | ~ (v1_funct_1 @ X49)
% 0.68/0.88          | ~ (v1_relat_1 @ X49))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ 
% 0.68/0.88         (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ sk_A)
% 0.68/0.88        | ((sk_B_1) = (k1_xboole_0))
% 0.68/0.88        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.68/0.88        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['48', '49'])).
% 0.68/0.88  thf('51', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (![X30 : $i]:
% 0.68/0.88         (~ (v2_funct_1 @ X30)
% 0.68/0.88          | ((k2_relat_1 @ X30) = (k1_relat_1 @ (k2_funct_1 @ X30)))
% 0.68/0.88          | ~ (v1_funct_1 @ X30)
% 0.68/0.88          | ~ (v1_relat_1 @ X30))),
% 0.68/0.88      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.68/0.88        | ~ (v1_relat_1 @ sk_C_1)
% 0.68/0.88        | ~ (v1_funct_1 @ sk_C_1)
% 0.68/0.88        | ~ (v2_funct_1 @ sk_C_1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['51', '52'])).
% 0.68/0.88  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.88  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('56', plain, ((v2_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k2_relset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.68/0.88       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.68/0.88         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.68/0.88          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['58', '59'])).
% 0.68/0.88  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('62', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['60', '61'])).
% 0.68/0.88  thf('63', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['57', '62'])).
% 0.68/0.88  thf('64', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.68/0.88  thf(dt_k2_funct_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.88       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.68/0.88         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.68/0.88  thf('65', plain,
% 0.68/0.88      (![X29 : $i]:
% 0.68/0.88         ((v1_relat_1 @ (k2_funct_1 @ X29))
% 0.68/0.88          | ~ (v1_funct_1 @ X29)
% 0.68/0.88          | ~ (v1_relat_1 @ X29))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.68/0.88  thf('66', plain,
% 0.68/0.88      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.68/0.88        | ~ (v1_relat_1 @ sk_C_1)
% 0.68/0.88        | ~ (v1_funct_1 @ sk_C_1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['64', '65'])).
% 0.68/0.88  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.88  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('69', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.68/0.88  thf('70', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.68/0.88  thf('71', plain,
% 0.68/0.88      (![X29 : $i]:
% 0.68/0.88         ((v1_funct_1 @ (k2_funct_1 @ X29))
% 0.68/0.88          | ~ (v1_funct_1 @ X29)
% 0.68/0.88          | ~ (v1_relat_1 @ X29))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.68/0.88  thf('72', plain,
% 0.68/0.88      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 0.68/0.88        | ~ (v1_relat_1 @ sk_C_1)
% 0.68/0.88        | ~ (v1_funct_1 @ sk_C_1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['70', '71'])).
% 0.68/0.88  thf('73', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.88  thf('74', plain, ((v1_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('75', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.68/0.88  thf('76', plain,
% 0.68/0.88      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 0.68/0.88        | ((sk_B_1) = (k1_xboole_0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['50', '63', '69', '75'])).
% 0.68/0.88  thf('77', plain,
% 0.68/0.88      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 0.68/0.88         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('split', [status(esa)], ['9'])).
% 0.68/0.88  thf('78', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 0.68/0.88         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['77', '78'])).
% 0.68/0.88  thf('80', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.88  thf('81', plain,
% 0.68/0.88      (![X29 : $i]:
% 0.68/0.88         ((v1_funct_1 @ (k2_funct_1 @ X29))
% 0.68/0.88          | ~ (v1_funct_1 @ X29)
% 0.68/0.88          | ~ (v1_relat_1 @ X29))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.68/0.88  thf('82', plain,
% 0.68/0.88      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.68/0.88         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.68/0.88      inference('split', [status(esa)], ['9'])).
% 0.68/0.88  thf('83', plain,
% 0.68/0.88      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 0.68/0.88         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['81', '82'])).
% 0.68/0.88  thf('84', plain, ((v1_funct_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('85', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.68/0.88      inference('demod', [status(thm)], ['83', '84'])).
% 0.68/0.88  thf('86', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['80', '85'])).
% 0.68/0.88  thf('87', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.68/0.88  thf('88', plain,
% 0.68/0.88      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('split', [status(esa)], ['9'])).
% 0.68/0.88  thf('89', plain,
% 0.68/0.88      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.68/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['87', '88'])).
% 0.68/0.88  thf('90', plain,
% 0.68/0.88      (![X41 : $i, X42 : $i]:
% 0.68/0.88         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.68/0.88  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '4'])).
% 0.68/0.88  thf('92', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['90', '91'])).
% 0.68/0.88  thf('93', plain,
% 0.68/0.88      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.88  thf('94', plain,
% 0.68/0.88      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['1'])).
% 0.68/0.88  thf('95', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['93', '94'])).
% 0.68/0.88  thf('96', plain,
% 0.68/0.88      (((v1_xboole_0 @ sk_C_1)
% 0.68/0.88        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.88  thf('97', plain,
% 0.68/0.88      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.68/0.88        | ~ (v1_xboole_0 @ sk_B_1)
% 0.68/0.88        | (v1_xboole_0 @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['95', '96'])).
% 0.68/0.88  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '4'])).
% 0.68/0.88  thf('99', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['97', '98'])).
% 0.68/0.88  thf('100', plain,
% 0.68/0.88      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['92', '99'])).
% 0.68/0.88  thf(fc14_relat_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( v1_xboole_0 @ A ) =>
% 0.68/0.88       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 0.68/0.88         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.68/0.88  thf('101', plain,
% 0.68/0.88      (![X25 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ (k4_relat_1 @ X25)) | ~ (v1_xboole_0 @ X25))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc14_relat_1])).
% 0.68/0.88  thf('102', plain,
% 0.68/0.88      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.88  thf(t4_subset_1, axiom,
% 0.68/0.88    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.68/0.88  thf('103', plain,
% 0.68/0.88      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.68/0.88  thf('104', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['102', '103'])).
% 0.68/0.88  thf('105', plain,
% 0.68/0.88      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.68/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['87', '88'])).
% 0.68/0.88  thf('106', plain,
% 0.68/0.88      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['104', '105'])).
% 0.68/0.88  thf('107', plain,
% 0.68/0.88      ((~ (v1_xboole_0 @ sk_C_1))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['101', '106'])).
% 0.68/0.88  thf('108', plain,
% 0.68/0.88      ((![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['100', '107'])).
% 0.68/0.88  thf('109', plain,
% 0.68/0.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.88  thf('110', plain,
% 0.68/0.88      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['108', '109'])).
% 0.68/0.88  thf('111', plain,
% 0.68/0.88      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.68/0.88        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))),
% 0.68/0.88      inference('demod', [status(thm)], ['35', '46'])).
% 0.68/0.88  thf('112', plain,
% 0.68/0.88      ((((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['110', '111'])).
% 0.68/0.88  thf('113', plain,
% 0.68/0.88      (![X49 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X49 @ 
% 0.68/0.88           (k1_zfmisc_1 @ 
% 0.68/0.88            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))))
% 0.68/0.88          | ~ (v1_funct_1 @ X49)
% 0.68/0.88          | ~ (v1_relat_1 @ X49))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.68/0.88  thf('114', plain,
% 0.68/0.88      ((((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.68/0.88          (k1_zfmisc_1 @ 
% 0.68/0.88           (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ sk_A)))
% 0.68/0.88         | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.68/0.88         | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1))))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['112', '113'])).
% 0.68/0.88  thf('115', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.68/0.88      inference('demod', [status(thm)], ['57', '62'])).
% 0.68/0.88  thf('116', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.68/0.88  thf('117', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.68/0.88      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.68/0.88  thf('118', plain,
% 0.68/0.88      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.68/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.68/0.88      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.68/0.88  thf('119', plain,
% 0.68/0.88      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.68/0.88      inference('demod', [status(thm)], ['89', '118'])).
% 0.68/0.88  thf('120', plain,
% 0.68/0.88      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)) | 
% 0.68/0.88       ~
% 0.68/0.88       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.68/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 0.68/0.88       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.68/0.88      inference('split', [status(esa)], ['9'])).
% 0.68/0.88  thf('121', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('sat_resolution*', [status(thm)], ['86', '119', '120'])).
% 0.68/0.88  thf('122', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B_1 @ sk_A)),
% 0.68/0.88      inference('simpl_trail', [status(thm)], ['79', '121'])).
% 0.68/0.88  thf('123', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.68/0.88      inference('clc', [status(thm)], ['76', '122'])).
% 0.68/0.88  thf('124', plain,
% 0.68/0.88      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['1'])).
% 0.68/0.88  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '4'])).
% 0.68/0.88  thf('126', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.68/0.88      inference('demod', [status(thm)], ['27', '123', '124', '125'])).
% 0.68/0.88  thf('127', plain,
% 0.68/0.88      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.88  thf('128', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['126', '127'])).
% 0.68/0.88  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '4'])).
% 0.68/0.88  thf('130', plain,
% 0.68/0.88      (![X25 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ (k4_relat_1 @ X25)) | ~ (v1_xboole_0 @ X25))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc14_relat_1])).
% 0.68/0.88  thf('131', plain,
% 0.68/0.88      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.88  thf('132', plain,
% 0.68/0.88      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['130', '131'])).
% 0.68/0.88  thf('133', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['129', '132'])).
% 0.68/0.88  thf('134', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.68/0.88      inference('clc', [status(thm)], ['76', '122'])).
% 0.68/0.88  thf('135', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '4'])).
% 0.68/0.88  thf('136', plain,
% 0.68/0.88      ((![X0 : $i]:
% 0.68/0.88          (~ (v1_funct_2 @ k1_xboole_0 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0)))
% 0.68/0.88         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['20', '128', '133', '134', '135'])).
% 0.68/0.88  thf('137', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 0.68/0.88      inference('sat_resolution*', [status(thm)], ['86', '119', '120'])).
% 0.68/0.88  thf('138', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (v1_funct_2 @ k1_xboole_0 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.88      inference('simpl_trail', [status(thm)], ['136', '137'])).
% 0.68/0.88  thf('139', plain,
% 0.68/0.88      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.68/0.88  thf(t60_relat_1, axiom,
% 0.68/0.88    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.68/0.88     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.68/0.88  thf('140', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.68/0.88  thf(t4_funct_2, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.88       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.68/0.88         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.68/0.88           ( m1_subset_1 @
% 0.68/0.88             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.68/0.88  thf('141', plain,
% 0.68/0.88      (![X50 : $i, X51 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k2_relat_1 @ X50) @ X51)
% 0.68/0.88          | (v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ X51)
% 0.68/0.88          | ~ (v1_funct_1 @ X50)
% 0.68/0.88          | ~ (v1_relat_1 @ X50))),
% 0.68/0.88      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.68/0.88  thf('142', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.68/0.88          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.68/0.88          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['140', '141'])).
% 0.68/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.88  thf('143', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.68/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.88  thf(t45_ordinal1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.68/0.88       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.68/0.88  thf('144', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.68/0.88      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.68/0.88  thf('145', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.68/0.88      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.68/0.88  thf('146', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.68/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.68/0.88  thf('147', plain,
% 0.68/0.88      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.68/0.88      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 0.68/0.88  thf('148', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['139', '147'])).
% 0.68/0.88  thf('149', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.68/0.88      inference('clc', [status(thm)], ['138', '148'])).
% 0.68/0.88  thf('150', plain, ($false), inference('sup-', [status(thm)], ['5', '149'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
