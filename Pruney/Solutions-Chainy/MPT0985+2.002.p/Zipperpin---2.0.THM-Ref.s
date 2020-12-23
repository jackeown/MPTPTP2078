%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DAyR9J2Ucz

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:27 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  192 (2008 expanded)
%              Number of leaves         :   43 ( 608 expanded)
%              Depth                    :   22
%              Number of atoms          : 1273 (30609 expanded)
%              Number of equality atoms :   80 (1203 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

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

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('23',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X36: $i] :
      ( ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('48',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('50',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('57',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('58',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('63',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('64',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','55','61','67'])).

thf('69',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','68'])).

thf('70',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('71',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['43','44'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('77',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('85',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('87',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','89'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('91',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('92',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('95',plain,(
    ! [X28: $i] :
      ( zip_tseitin_0 @ X28 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('97',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('101',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( v1_partfun1 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('102',plain,(
    ! [X1: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('103',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('104',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('105',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ X23 )
      | ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( X1
        = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('116',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','116'])).

thf('118',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30
       != ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('122',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['74','85','90','122'])).

thf('124',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('125',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['18','123','124'])).

thf('126',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['11','125'])).

thf('127',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('128',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('129',plain,(
    ! [X36: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('130',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('132',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('133',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('134',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['127','134'])).

thf('136',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['11','125'])).

thf('137',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','137'])).

thf('139',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('140',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['135','136'])).

thf('141',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('142',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('144',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','89'])).

thf('146',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('147',plain,(
    $false ),
    inference(demod,[status(thm)],['138','144','145','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DAyR9J2Ucz
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:18:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.52/1.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.52/1.72  % Solved by: fo/fo7.sh
% 1.52/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.52/1.72  % done 1298 iterations in 1.274s
% 1.52/1.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.52/1.72  % SZS output start Refutation
% 1.52/1.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.52/1.72  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.52/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.52/1.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.52/1.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.52/1.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.52/1.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.52/1.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.52/1.72  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.52/1.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.52/1.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.52/1.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.52/1.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.52/1.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.52/1.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.52/1.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.52/1.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.52/1.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.52/1.72  thf(sk_B_type, type, sk_B: $i).
% 1.52/1.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.52/1.72  thf(sk_C_type, type, sk_C: $i).
% 1.52/1.72  thf(t31_funct_2, conjecture,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.72       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.52/1.72         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.52/1.72           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.52/1.72           ( m1_subset_1 @
% 1.52/1.72             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.52/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.52/1.72    (~( ![A:$i,B:$i,C:$i]:
% 1.52/1.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.72          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.52/1.72            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.52/1.72              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.52/1.72              ( m1_subset_1 @
% 1.52/1.72                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.52/1.72    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.52/1.72  thf('0', plain,
% 1.52/1.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.52/1.72        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.52/1.72        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('1', plain,
% 1.52/1.72      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.52/1.72         <= (~
% 1.52/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.52/1.72      inference('split', [status(esa)], ['0'])).
% 1.52/1.72  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(d9_funct_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.52/1.72       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.52/1.72  thf('3', plain,
% 1.52/1.72      (![X10 : $i]:
% 1.52/1.72         (~ (v2_funct_1 @ X10)
% 1.52/1.72          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 1.52/1.72          | ~ (v1_funct_1 @ X10)
% 1.52/1.72          | ~ (v1_relat_1 @ X10))),
% 1.52/1.72      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.52/1.72  thf('4', plain,
% 1.52/1.72      ((~ (v1_relat_1 @ sk_C)
% 1.52/1.72        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.52/1.72        | ~ (v2_funct_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.52/1.72  thf('5', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('6', plain,
% 1.52/1.72      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 1.52/1.72      inference('demod', [status(thm)], ['4', '5'])).
% 1.52/1.72  thf('7', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(cc1_relset_1, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( v1_relat_1 @ C ) ))).
% 1.52/1.72  thf('8', plain,
% 1.52/1.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.52/1.72         ((v1_relat_1 @ X13)
% 1.52/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.52/1.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.52/1.72  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.72  thf('10', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '9'])).
% 1.52/1.72  thf('11', plain,
% 1.52/1.72      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.52/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.52/1.72         <= (~
% 1.52/1.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.52/1.72      inference('demod', [status(thm)], ['1', '10'])).
% 1.52/1.72  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.72  thf(dt_k2_funct_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.52/1.72       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.52/1.72         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.52/1.72  thf('13', plain,
% 1.52/1.72      (![X11 : $i]:
% 1.52/1.72         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 1.52/1.72          | ~ (v1_funct_1 @ X11)
% 1.52/1.72          | ~ (v1_relat_1 @ X11))),
% 1.52/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.52/1.72  thf('14', plain,
% 1.52/1.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.52/1.72         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.52/1.72      inference('split', [status(esa)], ['0'])).
% 1.52/1.72  thf('15', plain,
% 1.52/1.72      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.52/1.72         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.52/1.72      inference('sup-', [status(thm)], ['13', '14'])).
% 1.52/1.72  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('17', plain,
% 1.52/1.72      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.52/1.72      inference('demod', [status(thm)], ['15', '16'])).
% 1.52/1.72  thf('18', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['12', '17'])).
% 1.52/1.72  thf('19', plain,
% 1.52/1.72      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('split', [status(esa)], ['0'])).
% 1.52/1.72  thf('20', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '9'])).
% 1.52/1.72  thf(d1_funct_2, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.52/1.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.52/1.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.52/1.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.52/1.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.52/1.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.52/1.72  thf(zf_stmt_1, axiom,
% 1.52/1.72    (![B:$i,A:$i]:
% 1.52/1.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.52/1.72       ( zip_tseitin_0 @ B @ A ) ))).
% 1.52/1.72  thf('21', plain,
% 1.52/1.72      (![X28 : $i, X29 : $i]:
% 1.52/1.72         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.52/1.72  thf('22', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.52/1.72  thf(zf_stmt_3, axiom,
% 1.52/1.72    (![C:$i,B:$i,A:$i]:
% 1.52/1.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.52/1.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.52/1.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.52/1.72  thf(zf_stmt_5, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.52/1.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.52/1.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.52/1.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.52/1.72  thf('23', plain,
% 1.52/1.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.52/1.72         (~ (zip_tseitin_0 @ X33 @ X34)
% 1.52/1.72          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 1.52/1.72          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.52/1.72  thf('24', plain,
% 1.52/1.72      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.52/1.72      inference('sup-', [status(thm)], ['22', '23'])).
% 1.52/1.72  thf('25', plain,
% 1.52/1.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.52/1.72      inference('sup-', [status(thm)], ['21', '24'])).
% 1.52/1.72  thf('26', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('27', plain,
% 1.52/1.72      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.52/1.72         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 1.52/1.72          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 1.52/1.72          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.52/1.72  thf('28', plain,
% 1.52/1.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.52/1.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['26', '27'])).
% 1.52/1.72  thf('29', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(redefinition_k1_relset_1, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.52/1.72  thf('30', plain,
% 1.52/1.72      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.52/1.72         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.52/1.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.52/1.72  thf('31', plain,
% 1.52/1.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['29', '30'])).
% 1.52/1.72  thf('32', plain,
% 1.52/1.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.52/1.72      inference('demod', [status(thm)], ['28', '31'])).
% 1.52/1.72  thf('33', plain,
% 1.52/1.72      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['25', '32'])).
% 1.52/1.72  thf('34', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '9'])).
% 1.52/1.72  thf(t55_funct_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.52/1.72       ( ( v2_funct_1 @ A ) =>
% 1.52/1.72         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.52/1.72           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.52/1.72  thf('35', plain,
% 1.52/1.72      (![X12 : $i]:
% 1.52/1.72         (~ (v2_funct_1 @ X12)
% 1.52/1.72          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 1.52/1.72          | ~ (v1_funct_1 @ X12)
% 1.52/1.72          | ~ (v1_relat_1 @ X12))),
% 1.52/1.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.52/1.72  thf('36', plain,
% 1.52/1.72      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.52/1.72        | ~ (v1_relat_1 @ sk_C)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.72        | ~ (v2_funct_1 @ sk_C))),
% 1.52/1.72      inference('sup+', [status(thm)], ['34', '35'])).
% 1.52/1.72  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.72  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('40', plain,
% 1.52/1.72      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.52/1.72      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 1.52/1.72  thf('41', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(redefinition_k2_relset_1, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.52/1.72  thf('42', plain,
% 1.52/1.72      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.52/1.72         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 1.52/1.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.52/1.72  thf('43', plain,
% 1.52/1.72      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['41', '42'])).
% 1.52/1.72  thf('44', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('45', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.52/1.72      inference('sup+', [status(thm)], ['43', '44'])).
% 1.52/1.72  thf('46', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.52/1.72      inference('demod', [status(thm)], ['40', '45'])).
% 1.52/1.72  thf(t3_funct_2, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.52/1.72       ( ( v1_funct_1 @ A ) & 
% 1.52/1.72         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.52/1.72         ( m1_subset_1 @
% 1.52/1.72           A @ 
% 1.52/1.72           ( k1_zfmisc_1 @
% 1.52/1.72             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.52/1.72  thf('47', plain,
% 1.52/1.72      (![X36 : $i]:
% 1.52/1.72         ((v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))
% 1.52/1.72          | ~ (v1_funct_1 @ X36)
% 1.52/1.72          | ~ (v1_relat_1 @ X36))),
% 1.52/1.72      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.52/1.72  thf('48', plain,
% 1.52/1.72      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ 
% 1.52/1.72         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.52/1.72        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.52/1.72        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 1.52/1.72      inference('sup+', [status(thm)], ['46', '47'])).
% 1.52/1.72  thf('49', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '9'])).
% 1.52/1.72  thf('50', plain,
% 1.52/1.72      (![X12 : $i]:
% 1.52/1.72         (~ (v2_funct_1 @ X12)
% 1.52/1.72          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 1.52/1.72          | ~ (v1_funct_1 @ X12)
% 1.52/1.72          | ~ (v1_relat_1 @ X12))),
% 1.52/1.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.52/1.72  thf('51', plain,
% 1.52/1.72      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.52/1.72        | ~ (v1_relat_1 @ sk_C)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.72        | ~ (v2_funct_1 @ sk_C))),
% 1.52/1.72      inference('sup+', [status(thm)], ['49', '50'])).
% 1.52/1.72  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.72  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('54', plain, ((v2_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('55', plain,
% 1.52/1.72      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.52/1.72      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 1.52/1.72  thf('56', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '9'])).
% 1.52/1.72  thf('57', plain,
% 1.52/1.72      (![X11 : $i]:
% 1.52/1.72         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.52/1.72          | ~ (v1_funct_1 @ X11)
% 1.52/1.72          | ~ (v1_relat_1 @ X11))),
% 1.52/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.52/1.72  thf('58', plain,
% 1.52/1.72      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.52/1.72        | ~ (v1_relat_1 @ sk_C)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_C))),
% 1.52/1.72      inference('sup+', [status(thm)], ['56', '57'])).
% 1.52/1.72  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.72  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('61', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.52/1.72  thf('62', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '9'])).
% 1.52/1.72  thf('63', plain,
% 1.52/1.72      (![X11 : $i]:
% 1.52/1.72         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 1.52/1.72          | ~ (v1_funct_1 @ X11)
% 1.52/1.72          | ~ (v1_relat_1 @ X11))),
% 1.52/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.52/1.72  thf('64', plain,
% 1.52/1.72      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 1.52/1.72        | ~ (v1_relat_1 @ sk_C)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_C))),
% 1.52/1.72      inference('sup+', [status(thm)], ['62', '63'])).
% 1.52/1.72  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.72  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('67', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.52/1.72  thf('68', plain,
% 1.52/1.72      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['48', '55', '61', '67'])).
% 1.52/1.72  thf('69', plain,
% 1.52/1.72      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 1.52/1.72        | ((sk_B) = (k1_xboole_0)))),
% 1.52/1.72      inference('sup+', [status(thm)], ['33', '68'])).
% 1.52/1.72  thf('70', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '9'])).
% 1.52/1.72  thf('71', plain,
% 1.52/1.72      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('split', [status(esa)], ['0'])).
% 1.52/1.72  thf('72', plain,
% 1.52/1.72      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['70', '71'])).
% 1.52/1.72  thf('73', plain,
% 1.52/1.72      ((((sk_B) = (k1_xboole_0)))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['69', '72'])).
% 1.52/1.72  thf('74', plain,
% 1.52/1.72      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('demod', [status(thm)], ['19', '20', '73'])).
% 1.52/1.72  thf('75', plain,
% 1.52/1.72      ((((sk_B) = (k1_xboole_0)))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['69', '72'])).
% 1.52/1.72  thf('76', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.52/1.72      inference('sup+', [status(thm)], ['43', '44'])).
% 1.52/1.72  thf(fc9_relat_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.52/1.72       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 1.52/1.72  thf('77', plain,
% 1.52/1.72      (![X7 : $i]:
% 1.52/1.72         (~ (v1_xboole_0 @ (k2_relat_1 @ X7))
% 1.52/1.72          | ~ (v1_relat_1 @ X7)
% 1.52/1.72          | (v1_xboole_0 @ X7))),
% 1.52/1.72      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.52/1.72  thf('78', plain,
% 1.52/1.72      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['76', '77'])).
% 1.52/1.72  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('sup-', [status(thm)], ['7', '8'])).
% 1.52/1.72  thf('80', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 1.52/1.72      inference('demod', [status(thm)], ['78', '79'])).
% 1.52/1.72  thf('81', plain,
% 1.52/1.72      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['75', '80'])).
% 1.52/1.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.52/1.72  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.52/1.72  thf('83', plain,
% 1.52/1.72      (((v1_xboole_0 @ sk_C))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('demod', [status(thm)], ['81', '82'])).
% 1.52/1.72  thf(l13_xboole_0, axiom,
% 1.52/1.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.52/1.72  thf('84', plain,
% 1.52/1.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.52/1.72  thf('85', plain,
% 1.52/1.72      ((((sk_C) = (k1_xboole_0)))
% 1.52/1.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['83', '84'])).
% 1.52/1.72  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.52/1.72  thf(fc14_relat_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( v1_xboole_0 @ A ) =>
% 1.52/1.72       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 1.52/1.72         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 1.52/1.72  thf('87', plain,
% 1.52/1.72      (![X6 : $i]: ((v1_xboole_0 @ (k4_relat_1 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 1.52/1.72      inference('cnf', [status(esa)], [fc14_relat_1])).
% 1.52/1.72  thf('88', plain,
% 1.52/1.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.52/1.72  thf('89', plain,
% 1.52/1.72      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['87', '88'])).
% 1.52/1.72  thf('90', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.52/1.72      inference('sup-', [status(thm)], ['86', '89'])).
% 1.52/1.72  thf(t4_subset_1, axiom,
% 1.52/1.72    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.52/1.72  thf('91', plain,
% 1.52/1.72      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 1.52/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.52/1.72  thf('92', plain,
% 1.52/1.72      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.52/1.72         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.52/1.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.52/1.72  thf('93', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.52/1.72      inference('sup-', [status(thm)], ['91', '92'])).
% 1.52/1.72  thf('94', plain,
% 1.52/1.72      (![X28 : $i, X29 : $i]:
% 1.52/1.72         ((zip_tseitin_0 @ X28 @ X29) | ((X29) != (k1_xboole_0)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.52/1.72  thf('95', plain, (![X28 : $i]: (zip_tseitin_0 @ X28 @ k1_xboole_0)),
% 1.52/1.72      inference('simplify', [status(thm)], ['94'])).
% 1.52/1.72  thf('96', plain,
% 1.52/1.72      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 1.52/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.52/1.72  thf('97', plain,
% 1.52/1.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.52/1.72         (~ (zip_tseitin_0 @ X33 @ X34)
% 1.52/1.72          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 1.52/1.72          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.52/1.72  thf('98', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.52/1.72      inference('sup-', [status(thm)], ['96', '97'])).
% 1.52/1.72  thf('99', plain,
% 1.52/1.72      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.52/1.72      inference('sup-', [status(thm)], ['95', '98'])).
% 1.52/1.72  thf('100', plain,
% 1.52/1.72      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 1.52/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.52/1.72  thf(cc1_partfun1, axiom,
% 1.52/1.72    (![A:$i,B:$i]:
% 1.52/1.72     ( ( v1_xboole_0 @ A ) =>
% 1.52/1.72       ( ![C:$i]:
% 1.52/1.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.52/1.72  thf('101', plain,
% 1.52/1.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.52/1.72         (~ (v1_xboole_0 @ X25)
% 1.52/1.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 1.52/1.72          | (v1_partfun1 @ X26 @ X25))),
% 1.52/1.72      inference('cnf', [status(esa)], [cc1_partfun1])).
% 1.52/1.72  thf('102', plain,
% 1.52/1.72      (![X1 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.52/1.72      inference('sup-', [status(thm)], ['100', '101'])).
% 1.52/1.72  thf(cc1_funct_1, axiom,
% 1.52/1.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 1.52/1.72  thf('103', plain, (![X8 : $i]: ((v1_funct_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 1.52/1.72      inference('cnf', [status(esa)], [cc1_funct_1])).
% 1.52/1.72  thf('104', plain,
% 1.52/1.72      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 1.52/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.52/1.72  thf(cc1_funct_2, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.52/1.72         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.52/1.72  thf('105', plain,
% 1.52/1.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.52/1.72         (~ (v1_funct_1 @ X22)
% 1.52/1.72          | ~ (v1_partfun1 @ X22 @ X23)
% 1.52/1.72          | (v1_funct_2 @ X22 @ X23 @ X24)
% 1.52/1.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.52/1.72      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.52/1.72  thf('106', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 1.52/1.72          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 1.52/1.72          | ~ (v1_funct_1 @ k1_xboole_0))),
% 1.52/1.72      inference('sup-', [status(thm)], ['104', '105'])).
% 1.52/1.72  thf('107', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.52/1.72          | ~ (v1_partfun1 @ k1_xboole_0 @ X0)
% 1.52/1.72          | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 1.52/1.72      inference('sup-', [status(thm)], ['103', '106'])).
% 1.52/1.72  thf('108', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.52/1.72  thf('109', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         (~ (v1_partfun1 @ k1_xboole_0 @ X0)
% 1.52/1.72          | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 1.52/1.72      inference('demod', [status(thm)], ['107', '108'])).
% 1.52/1.72  thf('110', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         (~ (v1_xboole_0 @ X0) | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 1.52/1.72      inference('sup-', [status(thm)], ['102', '109'])).
% 1.52/1.72  thf('111', plain,
% 1.52/1.72      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.52/1.72         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 1.52/1.72          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 1.52/1.72          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.52/1.72  thf('112', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         (~ (v1_xboole_0 @ X1)
% 1.52/1.72          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.52/1.72          | ((X1) = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['110', '111'])).
% 1.52/1.72  thf('113', plain,
% 1.52/1.72      (![X0 : $i]:
% 1.52/1.72         (((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))
% 1.52/1.72          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.52/1.72      inference('sup-', [status(thm)], ['99', '112'])).
% 1.52/1.73  thf('114', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]:
% 1.52/1.73         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['91', '92'])).
% 1.52/1.73  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.52/1.73  thf('116', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.52/1.73      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.52/1.73  thf('117', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]:
% 1.52/1.73         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.52/1.73      inference('demod', [status(thm)], ['93', '116'])).
% 1.52/1.73  thf('118', plain,
% 1.52/1.73      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.52/1.73         (((X30) != (k1_relset_1 @ X30 @ X31 @ X32))
% 1.52/1.73          | (v1_funct_2 @ X32 @ X30 @ X31)
% 1.52/1.73          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.52/1.73  thf('119', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]:
% 1.52/1.73         (((X1) != (k1_xboole_0))
% 1.52/1.73          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.52/1.73          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['117', '118'])).
% 1.52/1.73  thf('120', plain,
% 1.52/1.73      (![X0 : $i]:
% 1.52/1.73         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.52/1.73          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.52/1.73      inference('simplify', [status(thm)], ['119'])).
% 1.52/1.73  thf('121', plain,
% 1.52/1.73      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.52/1.73      inference('sup-', [status(thm)], ['95', '98'])).
% 1.52/1.73  thf('122', plain,
% 1.52/1.73      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.52/1.73      inference('simplify_reflect+', [status(thm)], ['120', '121'])).
% 1.52/1.73  thf('123', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.52/1.73      inference('demod', [status(thm)], ['74', '85', '90', '122'])).
% 1.52/1.73  thf('124', plain,
% 1.52/1.73      (~
% 1.52/1.73       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.52/1.73       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.52/1.73       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.52/1.73      inference('split', [status(esa)], ['0'])).
% 1.52/1.73  thf('125', plain,
% 1.52/1.73      (~
% 1.52/1.73       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.52/1.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.52/1.73      inference('sat_resolution*', [status(thm)], ['18', '123', '124'])).
% 1.52/1.73  thf('126', plain,
% 1.52/1.73      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.52/1.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.73      inference('simpl_trail', [status(thm)], ['11', '125'])).
% 1.52/1.73  thf('127', plain,
% 1.52/1.73      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.52/1.73      inference('sup-', [status(thm)], ['25', '32'])).
% 1.52/1.73  thf('128', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.52/1.73      inference('demod', [status(thm)], ['40', '45'])).
% 1.52/1.73  thf('129', plain,
% 1.52/1.73      (![X36 : $i]:
% 1.52/1.73         ((m1_subset_1 @ X36 @ 
% 1.52/1.73           (k1_zfmisc_1 @ 
% 1.52/1.73            (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))))
% 1.52/1.73          | ~ (v1_funct_1 @ X36)
% 1.52/1.73          | ~ (v1_relat_1 @ X36))),
% 1.52/1.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.52/1.73  thf('130', plain,
% 1.52/1.73      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.52/1.73         (k1_zfmisc_1 @ 
% 1.52/1.73          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))))
% 1.52/1.73        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.52/1.73        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 1.52/1.73      inference('sup+', [status(thm)], ['128', '129'])).
% 1.52/1.73  thf('131', plain,
% 1.52/1.73      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.52/1.73      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 1.52/1.73  thf('132', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.52/1.73      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.52/1.73  thf('133', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 1.52/1.73      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.52/1.73  thf('134', plain,
% 1.52/1.73      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.52/1.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 1.52/1.73      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 1.52/1.73  thf('135', plain,
% 1.52/1.73      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.52/1.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.52/1.73        | ((sk_B) = (k1_xboole_0)))),
% 1.52/1.73      inference('sup+', [status(thm)], ['127', '134'])).
% 1.52/1.73  thf('136', plain,
% 1.52/1.73      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.52/1.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.73      inference('simpl_trail', [status(thm)], ['11', '125'])).
% 1.52/1.73  thf('137', plain, (((sk_B) = (k1_xboole_0))),
% 1.52/1.73      inference('clc', [status(thm)], ['135', '136'])).
% 1.52/1.73  thf('138', plain,
% 1.52/1.73      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.52/1.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 1.52/1.73      inference('demod', [status(thm)], ['126', '137'])).
% 1.52/1.73  thf('139', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 1.52/1.73      inference('demod', [status(thm)], ['78', '79'])).
% 1.52/1.73  thf('140', plain, (((sk_B) = (k1_xboole_0))),
% 1.52/1.73      inference('clc', [status(thm)], ['135', '136'])).
% 1.52/1.73  thf('141', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.52/1.73  thf('142', plain, ((v1_xboole_0 @ sk_C)),
% 1.52/1.73      inference('demod', [status(thm)], ['139', '140', '141'])).
% 1.52/1.73  thf('143', plain,
% 1.52/1.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.52/1.73  thf('144', plain, (((sk_C) = (k1_xboole_0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['142', '143'])).
% 1.52/1.73  thf('145', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['86', '89'])).
% 1.52/1.73  thf('146', plain,
% 1.52/1.73      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 1.52/1.73      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.52/1.73  thf('147', plain, ($false),
% 1.52/1.73      inference('demod', [status(thm)], ['138', '144', '145', '146'])).
% 1.52/1.73  
% 1.52/1.73  % SZS output end Refutation
% 1.52/1.73  
% 1.52/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
