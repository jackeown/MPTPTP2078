%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QEkVRiqMmd

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:43 EST 2020

% Result     : Theorem 39.73s
% Output     : Refutation 39.73s
% Verified   : 
% Statistics : Number of formulae       :  287 (2891 expanded)
%              Number of leaves         :   49 ( 872 expanded)
%              Depth                    :   37
%              Number of atoms          : 2268 (40226 expanded)
%              Number of equality atoms :  136 (2090 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k2_partfun1 @ X52 @ X53 @ X51 @ X54 )
        = ( k7_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['12','17','18'])).

thf('20',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v4_relat_1 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('27',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('31',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('34',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('46',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','55'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('60',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('63',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k2_partfun1 @ X52 @ X53 @ X51 @ X54 )
        = ( k7_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('68',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X28 @ X29 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('72',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','74'])).

thf('76',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('82',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_C @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('89',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('91',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80','89','90','91'])).

thf('93',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('97',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('99',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('102',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('107',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X42 @ X40 )
        = ( k1_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('110',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v4_relat_1 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('112',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','72'])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('117',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','117'])).

thf('119',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45
       != ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X44 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('123',plain,(
    ! [X43: $i] :
      ( zip_tseitin_0 @ X43 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('125',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['121','127'])).

thf('129',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['105','128'])).

thf('130',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('132',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['19','95','129','130','131'])).

thf('133',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','133'])).

thf('135',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','134'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('136',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('139',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('140',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['20','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('148',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X28 @ X29 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('154',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('156',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v5_relat_1 @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('159',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('162',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X28 @ X29 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('163',plain,
    ( ( r1_tarski @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('165',plain,(
    r1_tarski @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('169',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('171',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('175',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['160','175'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('177',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X55 ) @ X56 )
      | ( v1_funct_2 @ X55 @ ( k1_relat_1 @ X55 ) @ X56 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('181',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('182',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X21 )
        = ( k7_relat_1 @ X23 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('185',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('188',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('192',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('198',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('200',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['196','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('204',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['183','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('211',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('216',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['180','217'])).

thf('219',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['145','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('221',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('222',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['219','222'])).

thf('224',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('225',plain,(
    ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['19','223','224'])).

thf('226',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','225'])).

thf('227',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['20','144'])).

thf('228',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['160','175'])).

thf('229',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X55 ) @ X56 )
      | ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ X56 ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('234',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['227','234'])).

thf('236',plain,(
    $false ),
    inference(demod,[status(thm)],['226','235'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QEkVRiqMmd
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 39.73/39.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 39.73/39.98  % Solved by: fo/fo7.sh
% 39.73/39.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 39.73/39.98  % done 26070 iterations in 39.523s
% 39.73/39.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 39.73/39.98  % SZS output start Refutation
% 39.73/39.98  thf(sk_A_type, type, sk_A: $i).
% 39.73/39.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 39.73/39.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 39.73/39.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 39.73/39.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 39.73/39.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 39.73/39.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 39.73/39.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 39.73/39.98  thf(sk_C_type, type, sk_C: $i).
% 39.73/39.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 39.73/39.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 39.73/39.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 39.73/39.98  thf(sk_B_type, type, sk_B: $i).
% 39.73/39.98  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 39.73/39.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 39.73/39.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 39.73/39.98  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 39.73/39.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 39.73/39.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 39.73/39.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 39.73/39.98  thf(sk_D_type, type, sk_D: $i).
% 39.73/39.98  thf(t38_funct_2, conjecture,
% 39.73/39.98    (![A:$i,B:$i,C:$i,D:$i]:
% 39.73/39.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 39.73/39.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.73/39.98       ( ( r1_tarski @ C @ A ) =>
% 39.73/39.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 39.73/39.98           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 39.73/39.98             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 39.73/39.98             ( m1_subset_1 @
% 39.73/39.98               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 39.73/39.98               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 39.73/39.98  thf(zf_stmt_0, negated_conjecture,
% 39.73/39.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 39.73/39.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 39.73/39.98            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.73/39.98          ( ( r1_tarski @ C @ A ) =>
% 39.73/39.98            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 39.73/39.98              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 39.73/39.98                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 39.73/39.98                ( m1_subset_1 @
% 39.73/39.98                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 39.73/39.98                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 39.73/39.98    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 39.73/39.98  thf('0', plain,
% 39.73/39.98      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 39.73/39.98        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.73/39.98             sk_B)
% 39.73/39.98        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf('1', plain,
% 39.73/39.98      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 39.73/39.98         <= (~
% 39.73/39.98             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.98               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 39.73/39.98      inference('split', [status(esa)], ['0'])).
% 39.73/39.98  thf('2', plain,
% 39.73/39.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf(redefinition_k2_partfun1, axiom,
% 39.73/39.98    (![A:$i,B:$i,C:$i,D:$i]:
% 39.73/39.98     ( ( ( v1_funct_1 @ C ) & 
% 39.73/39.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.73/39.98       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 39.73/39.98  thf('3', plain,
% 39.73/39.98      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 39.73/39.98         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 39.73/39.98          | ~ (v1_funct_1 @ X51)
% 39.73/39.98          | ((k2_partfun1 @ X52 @ X53 @ X51 @ X54) = (k7_relat_1 @ X51 @ X54)))),
% 39.73/39.98      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 39.73/39.98  thf('4', plain,
% 39.73/39.98      (![X0 : $i]:
% 39.73/39.98         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 39.73/39.98          | ~ (v1_funct_1 @ sk_D))),
% 39.73/39.98      inference('sup-', [status(thm)], ['2', '3'])).
% 39.73/39.98  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf('6', plain,
% 39.73/39.98      (![X0 : $i]:
% 39.73/39.98         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.98      inference('demod', [status(thm)], ['4', '5'])).
% 39.73/39.98  thf('7', plain,
% 39.73/39.98      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 39.73/39.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 39.73/39.98         <= (~
% 39.73/39.98             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.98               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 39.73/39.98      inference('demod', [status(thm)], ['1', '6'])).
% 39.73/39.98  thf(fc8_funct_1, axiom,
% 39.73/39.98    (![A:$i,B:$i]:
% 39.73/39.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 39.73/39.98       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 39.73/39.98         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 39.73/39.98  thf('8', plain,
% 39.73/39.98      (![X35 : $i, X36 : $i]:
% 39.73/39.98         (~ (v1_funct_1 @ X35)
% 39.73/39.98          | ~ (v1_relat_1 @ X35)
% 39.73/39.98          | (v1_funct_1 @ (k7_relat_1 @ X35 @ X36)))),
% 39.73/39.98      inference('cnf', [status(esa)], [fc8_funct_1])).
% 39.73/39.98  thf('9', plain,
% 39.73/39.98      (![X0 : $i]:
% 39.73/39.98         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.98      inference('demod', [status(thm)], ['4', '5'])).
% 39.73/39.98  thf('10', plain,
% 39.73/39.98      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))
% 39.73/39.98         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 39.73/39.98      inference('split', [status(esa)], ['0'])).
% 39.73/39.98  thf('11', plain,
% 39.73/39.98      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ sk_C)))
% 39.73/39.98         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 39.73/39.98      inference('sup-', [status(thm)], ['9', '10'])).
% 39.73/39.98  thf('12', plain,
% 39.73/39.98      (((~ (v1_relat_1 @ sk_D) | ~ (v1_funct_1 @ sk_D)))
% 39.73/39.98         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 39.73/39.98      inference('sup-', [status(thm)], ['8', '11'])).
% 39.73/39.98  thf('13', plain,
% 39.73/39.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf(cc2_relat_1, axiom,
% 39.73/39.98    (![A:$i]:
% 39.73/39.98     ( ( v1_relat_1 @ A ) =>
% 39.73/39.98       ( ![B:$i]:
% 39.73/39.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 39.73/39.98  thf('14', plain,
% 39.73/39.98      (![X11 : $i, X12 : $i]:
% 39.73/39.98         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 39.73/39.98          | (v1_relat_1 @ X11)
% 39.73/39.98          | ~ (v1_relat_1 @ X12))),
% 39.73/39.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 39.73/39.98  thf('15', plain,
% 39.73/39.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 39.73/39.98      inference('sup-', [status(thm)], ['13', '14'])).
% 39.73/39.98  thf(fc6_relat_1, axiom,
% 39.73/39.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 39.73/39.98  thf('16', plain,
% 39.73/39.98      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 39.73/39.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 39.73/39.98  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.98      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.98  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf('19', plain,
% 39.73/39.98      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 39.73/39.98      inference('demod', [status(thm)], ['12', '17', '18'])).
% 39.73/39.98  thf('20', plain, ((r1_tarski @ sk_C @ sk_A)),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf('21', plain,
% 39.73/39.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf(cc2_relset_1, axiom,
% 39.73/39.98    (![A:$i,B:$i,C:$i]:
% 39.73/39.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.73/39.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 39.73/39.98  thf('22', plain,
% 39.73/39.98      (![X37 : $i, X38 : $i, X39 : $i]:
% 39.73/39.98         ((v4_relat_1 @ X37 @ X38)
% 39.73/39.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 39.73/39.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 39.73/39.98  thf('23', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 39.73/39.98      inference('sup-', [status(thm)], ['21', '22'])).
% 39.73/39.98  thf(t209_relat_1, axiom,
% 39.73/39.98    (![A:$i,B:$i]:
% 39.73/39.98     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 39.73/39.98       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 39.73/39.98  thf('24', plain,
% 39.73/39.98      (![X24 : $i, X25 : $i]:
% 39.73/39.98         (((X24) = (k7_relat_1 @ X24 @ X25))
% 39.73/39.98          | ~ (v4_relat_1 @ X24 @ X25)
% 39.73/39.98          | ~ (v1_relat_1 @ X24))),
% 39.73/39.98      inference('cnf', [status(esa)], [t209_relat_1])).
% 39.73/39.98  thf('25', plain,
% 39.73/39.98      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 39.73/39.98      inference('sup-', [status(thm)], ['23', '24'])).
% 39.73/39.98  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.98      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.98  thf('27', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 39.73/39.98      inference('demod', [status(thm)], ['25', '26'])).
% 39.73/39.98  thf(t89_relat_1, axiom,
% 39.73/39.98    (![A:$i,B:$i]:
% 39.73/39.98     ( ( v1_relat_1 @ B ) =>
% 39.73/39.98       ( r1_tarski @
% 39.73/39.98         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 39.73/39.98  thf('28', plain,
% 39.73/39.98      (![X30 : $i, X31 : $i]:
% 39.73/39.98         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X30 @ X31)) @ 
% 39.73/39.98           (k1_relat_1 @ X30))
% 39.73/39.98          | ~ (v1_relat_1 @ X30))),
% 39.73/39.98      inference('cnf', [status(esa)], [t89_relat_1])).
% 39.73/39.98  thf('29', plain,
% 39.73/39.98      (((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D))
% 39.73/39.98        | ~ (v1_relat_1 @ sk_D))),
% 39.73/39.98      inference('sup+', [status(thm)], ['27', '28'])).
% 39.73/39.98  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.98      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.98  thf('31', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D))),
% 39.73/39.98      inference('demod', [status(thm)], ['29', '30'])).
% 39.73/39.98  thf(d1_funct_2, axiom,
% 39.73/39.98    (![A:$i,B:$i,C:$i]:
% 39.73/39.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.73/39.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 39.73/39.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 39.73/39.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 39.73/39.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 39.73/39.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 39.73/39.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 39.73/39.98  thf(zf_stmt_1, axiom,
% 39.73/39.98    (![B:$i,A:$i]:
% 39.73/39.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 39.73/39.98       ( zip_tseitin_0 @ B @ A ) ))).
% 39.73/39.98  thf('32', plain,
% 39.73/39.98      (![X43 : $i, X44 : $i]:
% 39.73/39.98         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 39.73/39.98  thf('33', plain,
% 39.73/39.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 39.73/39.98  thf(zf_stmt_3, axiom,
% 39.73/39.98    (![C:$i,B:$i,A:$i]:
% 39.73/39.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 39.73/39.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 39.73/39.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 39.73/39.98  thf(zf_stmt_5, axiom,
% 39.73/39.98    (![A:$i,B:$i,C:$i]:
% 39.73/39.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.73/39.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 39.73/39.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 39.73/39.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 39.73/39.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 39.73/39.98  thf('34', plain,
% 39.73/39.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 39.73/39.98         (~ (zip_tseitin_0 @ X48 @ X49)
% 39.73/39.98          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 39.73/39.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 39.73/39.98  thf('35', plain,
% 39.73/39.98      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 39.73/39.98      inference('sup-', [status(thm)], ['33', '34'])).
% 39.73/39.98  thf('36', plain,
% 39.73/39.98      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 39.73/39.98      inference('sup-', [status(thm)], ['32', '35'])).
% 39.73/39.98  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf('38', plain,
% 39.73/39.98      (![X45 : $i, X46 : $i, X47 : $i]:
% 39.73/39.98         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 39.73/39.98          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 39.73/39.98          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 39.73/39.98  thf('39', plain,
% 39.73/39.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 39.73/39.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 39.73/39.98      inference('sup-', [status(thm)], ['37', '38'])).
% 39.73/39.98  thf('40', plain,
% 39.73/39.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf(redefinition_k1_relset_1, axiom,
% 39.73/39.98    (![A:$i,B:$i,C:$i]:
% 39.73/39.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.73/39.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 39.73/39.98  thf('41', plain,
% 39.73/39.98      (![X40 : $i, X41 : $i, X42 : $i]:
% 39.73/39.98         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 39.73/39.98          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 39.73/39.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 39.73/39.98  thf('42', plain,
% 39.73/39.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 39.73/39.98      inference('sup-', [status(thm)], ['40', '41'])).
% 39.73/39.98  thf('43', plain,
% 39.73/39.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 39.73/39.98      inference('demod', [status(thm)], ['39', '42'])).
% 39.73/39.98  thf('44', plain,
% 39.73/39.98      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 39.73/39.98      inference('sup-', [status(thm)], ['36', '43'])).
% 39.73/39.98  thf('45', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D))),
% 39.73/39.98      inference('demod', [status(thm)], ['29', '30'])).
% 39.73/39.98  thf('46', plain,
% 39.73/39.98      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 39.73/39.98      inference('sup+', [status(thm)], ['44', '45'])).
% 39.73/39.98  thf(t1_xboole_1, axiom,
% 39.73/39.98    (![A:$i,B:$i,C:$i]:
% 39.73/39.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 39.73/39.98       ( r1_tarski @ A @ C ) ))).
% 39.73/39.98  thf('47', plain,
% 39.73/39.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.98         (~ (r1_tarski @ X0 @ X1)
% 39.73/39.98          | ~ (r1_tarski @ X1 @ X2)
% 39.73/39.98          | (r1_tarski @ X0 @ X2))),
% 39.73/39.98      inference('cnf', [status(esa)], [t1_xboole_1])).
% 39.73/39.98  thf('48', plain,
% 39.73/39.98      (![X0 : $i]:
% 39.73/39.98         (((sk_B) = (k1_xboole_0))
% 39.73/39.98          | (r1_tarski @ sk_A @ X0)
% 39.73/39.98          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 39.73/39.98      inference('sup-', [status(thm)], ['46', '47'])).
% 39.73/39.98  thf('49', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.98  thf('50', plain,
% 39.73/39.98      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 39.73/39.98      inference('split', [status(esa)], ['49'])).
% 39.73/39.98  thf('51', plain,
% 39.73/39.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.98      inference('split', [status(esa)], ['49'])).
% 39.73/39.98  thf('52', plain,
% 39.73/39.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.73/39.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.99  thf('53', plain,
% 39.73/39.99      (((m1_subset_1 @ sk_D @ 
% 39.73/39.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 39.73/39.99         <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup+', [status(thm)], ['51', '52'])).
% 39.73/39.99  thf(t113_zfmisc_1, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 39.73/39.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 39.73/39.99  thf('54', plain,
% 39.73/39.99      (![X6 : $i, X7 : $i]:
% 39.73/39.99         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 39.73/39.99      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 39.73/39.99  thf('55', plain,
% 39.73/39.99      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 39.73/39.99      inference('simplify', [status(thm)], ['54'])).
% 39.73/39.99  thf('56', plain,
% 39.73/39.99      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 39.73/39.99         <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('demod', [status(thm)], ['53', '55'])).
% 39.73/39.99  thf(t3_subset, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 39.73/39.99  thf('57', plain,
% 39.73/39.99      (![X8 : $i, X9 : $i]:
% 39.73/39.99         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_subset])).
% 39.73/39.99  thf('58', plain,
% 39.73/39.99      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['56', '57'])).
% 39.73/39.99  thf(t3_xboole_1, axiom,
% 39.73/39.99    (![A:$i]:
% 39.73/39.99     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 39.73/39.99  thf('59', plain,
% 39.73/39.99      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_xboole_1])).
% 39.73/39.99  thf('60', plain,
% 39.73/39.99      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['58', '59'])).
% 39.73/39.99  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 39.73/39.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.99  thf('62', plain,
% 39.73/39.99      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup+', [status(thm)], ['60', '61'])).
% 39.73/39.99  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 39.73/39.99  thf('63', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 39.73/39.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 39.73/39.99  thf('64', plain,
% 39.73/39.99      (![X8 : $i, X10 : $i]:
% 39.73/39.99         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_subset])).
% 39.73/39.99  thf('65', plain,
% 39.73/39.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['63', '64'])).
% 39.73/39.99  thf('66', plain,
% 39.73/39.99      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 39.73/39.99         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 39.73/39.99          | ~ (v1_funct_1 @ X51)
% 39.73/39.99          | ((k2_partfun1 @ X52 @ X53 @ X51 @ X54) = (k7_relat_1 @ X51 @ X54)))),
% 39.73/39.99      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 39.73/39.99  thf('67', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 39.73/39.99            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 39.73/39.99          | ~ (v1_funct_1 @ k1_xboole_0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['65', '66'])).
% 39.73/39.99  thf(t88_relat_1, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 39.73/39.99  thf('68', plain,
% 39.73/39.99      (![X28 : $i, X29 : $i]:
% 39.73/39.99         ((r1_tarski @ (k7_relat_1 @ X28 @ X29) @ X28) | ~ (v1_relat_1 @ X28))),
% 39.73/39.99      inference('cnf', [status(esa)], [t88_relat_1])).
% 39.73/39.99  thf('69', plain,
% 39.73/39.99      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_xboole_1])).
% 39.73/39.99  thf('70', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ k1_xboole_0)
% 39.73/39.99          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 39.73/39.99      inference('sup-', [status(thm)], ['68', '69'])).
% 39.73/39.99  thf('71', plain,
% 39.73/39.99      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 39.73/39.99      inference('simplify', [status(thm)], ['54'])).
% 39.73/39.99  thf('72', plain,
% 39.73/39.99      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 39.73/39.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 39.73/39.99  thf('73', plain, ((v1_relat_1 @ k1_xboole_0)),
% 39.73/39.99      inference('sup+', [status(thm)], ['71', '72'])).
% 39.73/39.99  thf('74', plain,
% 39.73/39.99      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 39.73/39.99      inference('demod', [status(thm)], ['70', '73'])).
% 39.73/39.99  thf('75', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 39.73/39.99          | ~ (v1_funct_1 @ k1_xboole_0))),
% 39.73/39.99      inference('demod', [status(thm)], ['67', '74'])).
% 39.73/39.99  thf('76', plain,
% 39.73/39.99      ((![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 39.73/39.99         <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['62', '75'])).
% 39.73/39.99  thf('77', plain,
% 39.73/39.99      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('split', [status(esa)], ['49'])).
% 39.73/39.99  thf('78', plain,
% 39.73/39.99      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 39.73/39.99         <= (~
% 39.73/39.99             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 39.73/39.99      inference('split', [status(esa)], ['0'])).
% 39.73/39.99  thf('79', plain,
% 39.73/39.99      ((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 39.73/39.99         <= (~
% 39.73/39.99             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 39.73/39.99             (((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['77', '78'])).
% 39.73/39.99  thf('80', plain,
% 39.73/39.99      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['58', '59'])).
% 39.73/39.99  thf('81', plain,
% 39.73/39.99      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('split', [status(esa)], ['49'])).
% 39.73/39.99  thf('82', plain, ((r1_tarski @ sk_C @ sk_A)),
% 39.73/39.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.99  thf('83', plain,
% 39.73/39.99      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup+', [status(thm)], ['81', '82'])).
% 39.73/39.99  thf('84', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99         (~ (r1_tarski @ X0 @ X1)
% 39.73/39.99          | ~ (r1_tarski @ X1 @ X2)
% 39.73/39.99          | (r1_tarski @ X0 @ X2))),
% 39.73/39.99      inference('cnf', [status(esa)], [t1_xboole_1])).
% 39.73/39.99  thf('85', plain,
% 39.73/39.99      ((![X0 : $i]:
% 39.73/39.99          ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ k1_xboole_0 @ X0)))
% 39.73/39.99         <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['83', '84'])).
% 39.73/39.99  thf('86', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 39.73/39.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 39.73/39.99  thf('87', plain,
% 39.73/39.99      ((![X0 : $i]: (r1_tarski @ sk_C @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('demod', [status(thm)], ['85', '86'])).
% 39.73/39.99  thf('88', plain,
% 39.73/39.99      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_xboole_1])).
% 39.73/39.99  thf('89', plain,
% 39.73/39.99      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['87', '88'])).
% 39.73/39.99  thf('90', plain,
% 39.73/39.99      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['87', '88'])).
% 39.73/39.99  thf('91', plain,
% 39.73/39.99      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 39.73/39.99      inference('simplify', [status(thm)], ['54'])).
% 39.73/39.99  thf('92', plain,
% 39.73/39.99      ((~ (m1_subset_1 @ 
% 39.73/39.99           (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 39.73/39.99           (k1_zfmisc_1 @ k1_xboole_0)))
% 39.73/39.99         <= (~
% 39.73/39.99             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 39.73/39.99             (((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('demod', [status(thm)], ['79', '80', '89', '90', '91'])).
% 39.73/39.99  thf('93', plain,
% 39.73/39.99      ((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 39.73/39.99         <= (~
% 39.73/39.99             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 39.73/39.99             (((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['76', '92'])).
% 39.73/39.99  thf('94', plain,
% 39.73/39.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['63', '64'])).
% 39.73/39.99  thf('95', plain,
% 39.73/39.99      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 39.73/39.99       ~ (((sk_A) = (k1_xboole_0)))),
% 39.73/39.99      inference('demod', [status(thm)], ['93', '94'])).
% 39.73/39.99  thf('96', plain,
% 39.73/39.99      ((![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 39.73/39.99         <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['62', '75'])).
% 39.73/39.99  thf('97', plain,
% 39.73/39.99      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['58', '59'])).
% 39.73/39.99  thf('98', plain,
% 39.73/39.99      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('split', [status(esa)], ['49'])).
% 39.73/39.99  thf('99', plain,
% 39.73/39.99      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 39.73/39.99         <= (~
% 39.73/39.99             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.73/39.99               sk_B)))),
% 39.73/39.99      inference('split', [status(esa)], ['0'])).
% 39.73/39.99  thf('100', plain,
% 39.73/39.99      ((~ (v1_funct_2 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99           sk_C @ sk_B))
% 39.73/39.99         <= (~
% 39.73/39.99             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.73/39.99               sk_B)) & 
% 39.73/39.99             (((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['98', '99'])).
% 39.73/39.99  thf('101', plain,
% 39.73/39.99      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['87', '88'])).
% 39.73/39.99  thf('102', plain,
% 39.73/39.99      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['87', '88'])).
% 39.73/39.99  thf('103', plain,
% 39.73/39.99      ((~ (v1_funct_2 @ 
% 39.73/39.99           (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0) @ 
% 39.73/39.99           k1_xboole_0 @ sk_B))
% 39.73/39.99         <= (~
% 39.73/39.99             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.73/39.99               sk_B)) & 
% 39.73/39.99             (((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('demod', [status(thm)], ['100', '101', '102'])).
% 39.73/39.99  thf('104', plain,
% 39.73/39.99      ((~ (v1_funct_2 @ 
% 39.73/39.99           (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 39.73/39.99           k1_xboole_0 @ sk_B))
% 39.73/39.99         <= (~
% 39.73/39.99             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.73/39.99               sk_B)) & 
% 39.73/39.99             (((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['97', '103'])).
% 39.73/39.99  thf('105', plain,
% 39.73/39.99      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 39.73/39.99         <= (~
% 39.73/39.99             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.73/39.99               sk_B)) & 
% 39.73/39.99             (((sk_A) = (k1_xboole_0))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['96', '104'])).
% 39.73/39.99  thf('106', plain,
% 39.73/39.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['63', '64'])).
% 39.73/39.99  thf('107', plain,
% 39.73/39.99      (![X40 : $i, X41 : $i, X42 : $i]:
% 39.73/39.99         (((k1_relset_1 @ X41 @ X42 @ X40) = (k1_relat_1 @ X40))
% 39.73/39.99          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 39.73/39.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 39.73/39.99  thf('108', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i]:
% 39.73/39.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['106', '107'])).
% 39.73/39.99  thf('109', plain,
% 39.73/39.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['63', '64'])).
% 39.73/39.99  thf('110', plain,
% 39.73/39.99      (![X37 : $i, X38 : $i, X39 : $i]:
% 39.73/39.99         ((v4_relat_1 @ X37 @ X38)
% 39.73/39.99          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 39.73/39.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 39.73/39.99  thf('111', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 39.73/39.99      inference('sup-', [status(thm)], ['109', '110'])).
% 39.73/39.99  thf(d18_relat_1, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( v1_relat_1 @ B ) =>
% 39.73/39.99       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 39.73/39.99  thf('112', plain,
% 39.73/39.99      (![X13 : $i, X14 : $i]:
% 39.73/39.99         (~ (v4_relat_1 @ X13 @ X14)
% 39.73/39.99          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 39.73/39.99          | ~ (v1_relat_1 @ X13))),
% 39.73/39.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 39.73/39.99  thf('113', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ k1_xboole_0)
% 39.73/39.99          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['111', '112'])).
% 39.73/39.99  thf('114', plain, ((v1_relat_1 @ k1_xboole_0)),
% 39.73/39.99      inference('sup+', [status(thm)], ['71', '72'])).
% 39.73/39.99  thf('115', plain,
% 39.73/39.99      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 39.73/39.99      inference('demod', [status(thm)], ['113', '114'])).
% 39.73/39.99  thf('116', plain,
% 39.73/39.99      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_xboole_1])).
% 39.73/39.99  thf('117', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['115', '116'])).
% 39.73/39.99  thf('118', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i]:
% 39.73/39.99         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 39.73/39.99      inference('demod', [status(thm)], ['108', '117'])).
% 39.73/39.99  thf('119', plain,
% 39.73/39.99      (![X45 : $i, X46 : $i, X47 : $i]:
% 39.73/39.99         (((X45) != (k1_relset_1 @ X45 @ X46 @ X47))
% 39.73/39.99          | (v1_funct_2 @ X47 @ X45 @ X46)
% 39.73/39.99          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 39.73/39.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 39.73/39.99  thf('120', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i]:
% 39.73/39.99         (((X1) != (k1_xboole_0))
% 39.73/39.99          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 39.73/39.99          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['118', '119'])).
% 39.73/39.99  thf('121', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 39.73/39.99          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 39.73/39.99      inference('simplify', [status(thm)], ['120'])).
% 39.73/39.99  thf('122', plain,
% 39.73/39.99      (![X43 : $i, X44 : $i]:
% 39.73/39.99         ((zip_tseitin_0 @ X43 @ X44) | ((X44) != (k1_xboole_0)))),
% 39.73/39.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 39.73/39.99  thf('123', plain, (![X43 : $i]: (zip_tseitin_0 @ X43 @ k1_xboole_0)),
% 39.73/39.99      inference('simplify', [status(thm)], ['122'])).
% 39.73/39.99  thf('124', plain,
% 39.73/39.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 39.73/39.99      inference('sup-', [status(thm)], ['63', '64'])).
% 39.73/39.99  thf('125', plain,
% 39.73/39.99      (![X48 : $i, X49 : $i, X50 : $i]:
% 39.73/39.99         (~ (zip_tseitin_0 @ X48 @ X49)
% 39.73/39.99          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 39.73/39.99          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 39.73/39.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 39.73/39.99  thf('126', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i]:
% 39.73/39.99         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 39.73/39.99      inference('sup-', [status(thm)], ['124', '125'])).
% 39.73/39.99  thf('127', plain,
% 39.73/39.99      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 39.73/39.99      inference('sup-', [status(thm)], ['123', '126'])).
% 39.73/39.99  thf('128', plain,
% 39.73/39.99      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 39.73/39.99      inference('demod', [status(thm)], ['121', '127'])).
% 39.73/39.99  thf('129', plain,
% 39.73/39.99      (~ (((sk_A) = (k1_xboole_0))) | 
% 39.73/39.99       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 39.73/39.99      inference('demod', [status(thm)], ['105', '128'])).
% 39.73/39.99  thf('130', plain,
% 39.73/39.99      (~
% 39.73/39.99       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 39.73/39.99       ~
% 39.73/39.99       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 39.73/39.99       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 39.73/39.99      inference('split', [status(esa)], ['0'])).
% 39.73/39.99  thf('131', plain,
% 39.73/39.99      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 39.73/39.99      inference('split', [status(esa)], ['49'])).
% 39.73/39.99  thf('132', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 39.73/39.99      inference('sat_resolution*', [status(thm)],
% 39.73/39.99                ['19', '95', '129', '130', '131'])).
% 39.73/39.99  thf('133', plain, (((sk_B) != (k1_xboole_0))),
% 39.73/39.99      inference('simpl_trail', [status(thm)], ['50', '132'])).
% 39.73/39.99  thf('134', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 39.73/39.99      inference('simplify_reflect-', [status(thm)], ['48', '133'])).
% 39.73/39.99  thf('135', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_D))),
% 39.73/39.99      inference('sup-', [status(thm)], ['31', '134'])).
% 39.73/39.99  thf(t91_relat_1, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( v1_relat_1 @ B ) =>
% 39.73/39.99       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 39.73/39.99         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 39.73/39.99  thf('136', plain,
% 39.73/39.99      (![X32 : $i, X33 : $i]:
% 39.73/39.99         (~ (r1_tarski @ X32 @ (k1_relat_1 @ X33))
% 39.73/39.99          | ((k1_relat_1 @ (k7_relat_1 @ X33 @ X32)) = (X32))
% 39.73/39.99          | ~ (v1_relat_1 @ X33))),
% 39.73/39.99      inference('cnf', [status(esa)], [t91_relat_1])).
% 39.73/39.99  thf('137', plain,
% 39.73/39.99      ((~ (v1_relat_1 @ sk_D)
% 39.73/39.99        | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_A)) = (sk_A)))),
% 39.73/39.99      inference('sup-', [status(thm)], ['135', '136'])).
% 39.73/39.99  thf('138', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('139', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 39.73/39.99      inference('demod', [status(thm)], ['25', '26'])).
% 39.73/39.99  thf('140', plain, (((k1_relat_1 @ sk_D) = (sk_A))),
% 39.73/39.99      inference('demod', [status(thm)], ['137', '138', '139'])).
% 39.73/39.99  thf('141', plain,
% 39.73/39.99      (![X32 : $i, X33 : $i]:
% 39.73/39.99         (~ (r1_tarski @ X32 @ (k1_relat_1 @ X33))
% 39.73/39.99          | ((k1_relat_1 @ (k7_relat_1 @ X33 @ X32)) = (X32))
% 39.73/39.99          | ~ (v1_relat_1 @ X33))),
% 39.73/39.99      inference('cnf', [status(esa)], [t91_relat_1])).
% 39.73/39.99  thf('142', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (r1_tarski @ X0 @ sk_A)
% 39.73/39.99          | ~ (v1_relat_1 @ sk_D)
% 39.73/39.99          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 39.73/39.99      inference('sup-', [status(thm)], ['140', '141'])).
% 39.73/39.99  thf('143', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('144', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (r1_tarski @ X0 @ sk_A)
% 39.73/39.99          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 39.73/39.99      inference('demod', [status(thm)], ['142', '143'])).
% 39.73/39.99  thf('145', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 39.73/39.99      inference('sup-', [status(thm)], ['20', '144'])).
% 39.73/39.99  thf('146', plain,
% 39.73/39.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.73/39.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.99  thf('147', plain,
% 39.73/39.99      (![X8 : $i, X9 : $i]:
% 39.73/39.99         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_subset])).
% 39.73/39.99  thf('148', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 39.73/39.99      inference('sup-', [status(thm)], ['146', '147'])).
% 39.73/39.99  thf('149', plain,
% 39.73/39.99      (![X28 : $i, X29 : $i]:
% 39.73/39.99         ((r1_tarski @ (k7_relat_1 @ X28 @ X29) @ X28) | ~ (v1_relat_1 @ X28))),
% 39.73/39.99      inference('cnf', [status(esa)], [t88_relat_1])).
% 39.73/39.99  thf('150', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99         (~ (r1_tarski @ X0 @ X1)
% 39.73/39.99          | ~ (r1_tarski @ X1 @ X2)
% 39.73/39.99          | (r1_tarski @ X0 @ X2))),
% 39.73/39.99      inference('cnf', [status(esa)], [t1_xboole_1])).
% 39.73/39.99  thf('151', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ X0)
% 39.73/39.99          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 39.73/39.99          | ~ (r1_tarski @ X0 @ X2))),
% 39.73/39.99      inference('sup-', [status(thm)], ['149', '150'])).
% 39.73/39.99  thf('152', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 39.73/39.99          | ~ (v1_relat_1 @ sk_D))),
% 39.73/39.99      inference('sup-', [status(thm)], ['148', '151'])).
% 39.73/39.99  thf('153', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('154', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 39.73/39.99      inference('demod', [status(thm)], ['152', '153'])).
% 39.73/39.99  thf('155', plain,
% 39.73/39.99      (![X8 : $i, X10 : $i]:
% 39.73/39.99         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_subset])).
% 39.73/39.99  thf('156', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.73/39.99      inference('sup-', [status(thm)], ['154', '155'])).
% 39.73/39.99  thf('157', plain,
% 39.73/39.99      (![X37 : $i, X38 : $i, X39 : $i]:
% 39.73/39.99         ((v5_relat_1 @ X37 @ X39)
% 39.73/39.99          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 39.73/39.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 39.73/39.99  thf('158', plain,
% 39.73/39.99      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 39.73/39.99      inference('sup-', [status(thm)], ['156', '157'])).
% 39.73/39.99  thf(d19_relat_1, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( v1_relat_1 @ B ) =>
% 39.73/39.99       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 39.73/39.99  thf('159', plain,
% 39.73/39.99      (![X15 : $i, X16 : $i]:
% 39.73/39.99         (~ (v5_relat_1 @ X15 @ X16)
% 39.73/39.99          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 39.73/39.99          | ~ (v1_relat_1 @ X15))),
% 39.73/39.99      inference('cnf', [status(esa)], [d19_relat_1])).
% 39.73/39.99  thf('160', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 39.73/39.99      inference('sup-', [status(thm)], ['158', '159'])).
% 39.73/39.99  thf('161', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 39.73/39.99      inference('demod', [status(thm)], ['25', '26'])).
% 39.73/39.99  thf('162', plain,
% 39.73/39.99      (![X28 : $i, X29 : $i]:
% 39.73/39.99         ((r1_tarski @ (k7_relat_1 @ X28 @ X29) @ X28) | ~ (v1_relat_1 @ X28))),
% 39.73/39.99      inference('cnf', [status(esa)], [t88_relat_1])).
% 39.73/39.99  thf('163', plain, (((r1_tarski @ sk_D @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 39.73/39.99      inference('sup+', [status(thm)], ['161', '162'])).
% 39.73/39.99  thf('164', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('165', plain, ((r1_tarski @ sk_D @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['163', '164'])).
% 39.73/39.99  thf('166', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ X0)
% 39.73/39.99          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 39.73/39.99          | ~ (r1_tarski @ X0 @ X2))),
% 39.73/39.99      inference('sup-', [status(thm)], ['149', '150'])).
% 39.73/39.99  thf('167', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 39.73/39.99      inference('sup-', [status(thm)], ['165', '166'])).
% 39.73/39.99  thf('168', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('169', plain,
% 39.73/39.99      (![X0 : $i]: (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['167', '168'])).
% 39.73/39.99  thf('170', plain,
% 39.73/39.99      (![X8 : $i, X10 : $i]:
% 39.73/39.99         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 39.73/39.99      inference('cnf', [status(esa)], [t3_subset])).
% 39.73/39.99  thf('171', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ (k1_zfmisc_1 @ sk_D))),
% 39.73/39.99      inference('sup-', [status(thm)], ['169', '170'])).
% 39.73/39.99  thf('172', plain,
% 39.73/39.99      (![X11 : $i, X12 : $i]:
% 39.73/39.99         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 39.73/39.99          | (v1_relat_1 @ X11)
% 39.73/39.99          | ~ (v1_relat_1 @ X12))),
% 39.73/39.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 39.73/39.99  thf('173', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 39.73/39.99      inference('sup-', [status(thm)], ['171', '172'])).
% 39.73/39.99  thf('174', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('175', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['173', '174'])).
% 39.73/39.99  thf('176', plain,
% 39.73/39.99      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 39.73/39.99      inference('demod', [status(thm)], ['160', '175'])).
% 39.73/39.99  thf(t4_funct_2, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 39.73/39.99       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 39.73/39.99         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 39.73/39.99           ( m1_subset_1 @
% 39.73/39.99             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 39.73/39.99  thf('177', plain,
% 39.73/39.99      (![X55 : $i, X56 : $i]:
% 39.73/39.99         (~ (r1_tarski @ (k2_relat_1 @ X55) @ X56)
% 39.73/39.99          | (v1_funct_2 @ X55 @ (k1_relat_1 @ X55) @ X56)
% 39.73/39.99          | ~ (v1_funct_1 @ X55)
% 39.73/39.99          | ~ (v1_relat_1 @ X55))),
% 39.73/39.99      inference('cnf', [status(esa)], [t4_funct_2])).
% 39.73/39.99  thf('178', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 39.73/39.99      inference('sup-', [status(thm)], ['176', '177'])).
% 39.73/39.99  thf('179', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['173', '174'])).
% 39.73/39.99  thf('180', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 39.73/39.99      inference('demod', [status(thm)], ['178', '179'])).
% 39.73/39.99  thf(t87_relat_1, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( v1_relat_1 @ B ) =>
% 39.73/39.99       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 39.73/39.99  thf('181', plain,
% 39.73/39.99      (![X26 : $i, X27 : $i]:
% 39.73/39.99         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X26 @ X27)) @ X27)
% 39.73/39.99          | ~ (v1_relat_1 @ X26))),
% 39.73/39.99      inference('cnf', [status(esa)], [t87_relat_1])).
% 39.73/39.99  thf(t103_relat_1, axiom,
% 39.73/39.99    (![A:$i,B:$i,C:$i]:
% 39.73/39.99     ( ( v1_relat_1 @ C ) =>
% 39.73/39.99       ( ( r1_tarski @ A @ B ) =>
% 39.73/39.99         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 39.73/39.99  thf('182', plain,
% 39.73/39.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 39.73/39.99         (~ (r1_tarski @ X21 @ X22)
% 39.73/39.99          | ~ (v1_relat_1 @ X23)
% 39.73/39.99          | ((k7_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X21)
% 39.73/39.99              = (k7_relat_1 @ X23 @ X21)))),
% 39.73/39.99      inference('cnf', [status(esa)], [t103_relat_1])).
% 39.73/39.99  thf('183', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ X1)
% 39.73/39.99          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ 
% 39.73/39.99              (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 39.73/39.99              = (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 39.73/39.99          | ~ (v1_relat_1 @ X2))),
% 39.73/39.99      inference('sup-', [status(thm)], ['181', '182'])).
% 39.73/39.99  thf('184', plain, (((k1_relat_1 @ sk_D) = (sk_A))),
% 39.73/39.99      inference('demod', [status(thm)], ['137', '138', '139'])).
% 39.73/39.99  thf('185', plain,
% 39.73/39.99      (![X30 : $i, X31 : $i]:
% 39.73/39.99         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X30 @ X31)) @ 
% 39.73/39.99           (k1_relat_1 @ X30))
% 39.73/39.99          | ~ (v1_relat_1 @ X30))),
% 39.73/39.99      inference('cnf', [status(esa)], [t89_relat_1])).
% 39.73/39.99  thf('186', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_A)
% 39.73/39.99          | ~ (v1_relat_1 @ sk_D))),
% 39.73/39.99      inference('sup+', [status(thm)], ['184', '185'])).
% 39.73/39.99  thf('187', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('188', plain,
% 39.73/39.99      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_A)),
% 39.73/39.99      inference('demod', [status(thm)], ['186', '187'])).
% 39.73/39.99  thf('189', plain,
% 39.73/39.99      (![X13 : $i, X14 : $i]:
% 39.73/39.99         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 39.73/39.99          | (v4_relat_1 @ X13 @ X14)
% 39.73/39.99          | ~ (v1_relat_1 @ X13))),
% 39.73/39.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 39.73/39.99  thf('190', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_A))),
% 39.73/39.99      inference('sup-', [status(thm)], ['188', '189'])).
% 39.73/39.99  thf('191', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['173', '174'])).
% 39.73/39.99  thf('192', plain,
% 39.73/39.99      (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_A)),
% 39.73/39.99      inference('demod', [status(thm)], ['190', '191'])).
% 39.73/39.99  thf('193', plain,
% 39.73/39.99      (![X24 : $i, X25 : $i]:
% 39.73/39.99         (((X24) = (k7_relat_1 @ X24 @ X25))
% 39.73/39.99          | ~ (v4_relat_1 @ X24 @ X25)
% 39.73/39.99          | ~ (v1_relat_1 @ X24))),
% 39.73/39.99      inference('cnf', [status(esa)], [t209_relat_1])).
% 39.73/39.99  thf('194', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | ((k7_relat_1 @ sk_D @ X0)
% 39.73/39.99              = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_A)))),
% 39.73/39.99      inference('sup-', [status(thm)], ['192', '193'])).
% 39.73/39.99  thf('195', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['173', '174'])).
% 39.73/39.99  thf('196', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((k7_relat_1 @ sk_D @ X0)
% 39.73/39.99           = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_A))),
% 39.73/39.99      inference('demod', [status(thm)], ['194', '195'])).
% 39.73/39.99  thf('197', plain,
% 39.73/39.99      (![X30 : $i, X31 : $i]:
% 39.73/39.99         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X30 @ X31)) @ 
% 39.73/39.99           (k1_relat_1 @ X30))
% 39.73/39.99          | ~ (v1_relat_1 @ X30))),
% 39.73/39.99      inference('cnf', [status(esa)], [t89_relat_1])).
% 39.73/39.99  thf('198', plain,
% 39.73/39.99      (![X13 : $i, X14 : $i]:
% 39.73/39.99         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 39.73/39.99          | (v4_relat_1 @ X13 @ X14)
% 39.73/39.99          | ~ (v1_relat_1 @ X13))),
% 39.73/39.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 39.73/39.99  thf('199', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ X0)
% 39.73/39.99          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 39.73/39.99          | (v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 39.73/39.99      inference('sup-', [status(thm)], ['197', '198'])).
% 39.73/39.99  thf(dt_k7_relat_1, axiom,
% 39.73/39.99    (![A:$i,B:$i]:
% 39.73/39.99     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 39.73/39.99  thf('200', plain,
% 39.73/39.99      (![X17 : $i, X18 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 39.73/39.99      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 39.73/39.99  thf('201', plain,
% 39.73/39.99      (![X0 : $i, X1 : $i]:
% 39.73/39.99         ((v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 39.73/39.99          | ~ (v1_relat_1 @ X0))),
% 39.73/39.99      inference('clc', [status(thm)], ['199', '200'])).
% 39.73/39.99  thf('202', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99           (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 39.73/39.99          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 39.73/39.99      inference('sup+', [status(thm)], ['196', '201'])).
% 39.73/39.99  thf('203', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['173', '174'])).
% 39.73/39.99  thf('204', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 39.73/39.99      inference('demod', [status(thm)], ['202', '203'])).
% 39.73/39.99  thf('205', plain,
% 39.73/39.99      (![X24 : $i, X25 : $i]:
% 39.73/39.99         (((X24) = (k7_relat_1 @ X24 @ X25))
% 39.73/39.99          | ~ (v4_relat_1 @ X24 @ X25)
% 39.73/39.99          | ~ (v1_relat_1 @ X24))),
% 39.73/39.99      inference('cnf', [status(esa)], [t209_relat_1])).
% 39.73/39.99  thf('206', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | ((k7_relat_1 @ sk_D @ X0)
% 39.73/39.99              = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99                 (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['204', '205'])).
% 39.73/39.99  thf('207', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['173', '174'])).
% 39.73/39.99  thf('208', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((k7_relat_1 @ sk_D @ X0)
% 39.73/39.99           = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99              (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))))),
% 39.73/39.99      inference('demod', [status(thm)], ['206', '207'])).
% 39.73/39.99  thf('209', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (((k7_relat_1 @ sk_D @ X0)
% 39.73/39.99            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))))
% 39.73/39.99          | ~ (v1_relat_1 @ sk_D)
% 39.73/39.99          | ~ (v1_relat_1 @ sk_D))),
% 39.73/39.99      inference('sup+', [status(thm)], ['183', '208'])).
% 39.73/39.99  thf('210', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('211', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('212', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((k7_relat_1 @ sk_D @ X0)
% 39.73/39.99           = (k7_relat_1 @ sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))))),
% 39.73/39.99      inference('demod', [status(thm)], ['209', '210', '211'])).
% 39.73/39.99  thf('213', plain,
% 39.73/39.99      (![X35 : $i, X36 : $i]:
% 39.73/39.99         (~ (v1_funct_1 @ X35)
% 39.73/39.99          | ~ (v1_relat_1 @ X35)
% 39.73/39.99          | (v1_funct_1 @ (k7_relat_1 @ X35 @ X36)))),
% 39.73/39.99      inference('cnf', [status(esa)], [fc8_funct_1])).
% 39.73/39.99  thf('214', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | ~ (v1_relat_1 @ sk_D)
% 39.73/39.99          | ~ (v1_funct_1 @ sk_D))),
% 39.73/39.99      inference('sup+', [status(thm)], ['212', '213'])).
% 39.73/39.99  thf('215', plain, ((v1_relat_1 @ sk_D)),
% 39.73/39.99      inference('demod', [status(thm)], ['15', '16'])).
% 39.73/39.99  thf('216', plain, ((v1_funct_1 @ sk_D)),
% 39.73/39.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.73/39.99  thf('217', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['214', '215', '216'])).
% 39.73/39.99  thf('218', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 39.73/39.99      inference('demod', [status(thm)], ['180', '217'])).
% 39.73/39.99  thf('219', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 39.73/39.99      inference('sup+', [status(thm)], ['145', '218'])).
% 39.73/39.99  thf('220', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['4', '5'])).
% 39.73/39.99  thf('221', plain,
% 39.73/39.99      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 39.73/39.99         <= (~
% 39.73/39.99             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.73/39.99               sk_B)))),
% 39.73/39.99      inference('split', [status(esa)], ['0'])).
% 39.73/39.99  thf('222', plain,
% 39.73/39.99      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 39.73/39.99         <= (~
% 39.73/39.99             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 39.73/39.99               sk_B)))),
% 39.73/39.99      inference('sup-', [status(thm)], ['220', '221'])).
% 39.73/39.99  thf('223', plain,
% 39.73/39.99      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 39.73/39.99      inference('sup-', [status(thm)], ['219', '222'])).
% 39.73/39.99  thf('224', plain,
% 39.73/39.99      (~
% 39.73/39.99       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 39.73/39.99       ~
% 39.73/39.99       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 39.73/39.99       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 39.73/39.99      inference('split', [status(esa)], ['0'])).
% 39.73/39.99  thf('225', plain,
% 39.73/39.99      (~
% 39.73/39.99       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 39.73/39.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 39.73/39.99      inference('sat_resolution*', [status(thm)], ['19', '223', '224'])).
% 39.73/39.99  thf('226', plain,
% 39.73/39.99      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 39.73/39.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 39.73/39.99      inference('simpl_trail', [status(thm)], ['7', '225'])).
% 39.73/39.99  thf('227', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 39.73/39.99      inference('sup-', [status(thm)], ['20', '144'])).
% 39.73/39.99  thf('228', plain,
% 39.73/39.99      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 39.73/39.99      inference('demod', [status(thm)], ['160', '175'])).
% 39.73/39.99  thf('229', plain,
% 39.73/39.99      (![X55 : $i, X56 : $i]:
% 39.73/39.99         (~ (r1_tarski @ (k2_relat_1 @ X55) @ X56)
% 39.73/39.99          | (m1_subset_1 @ X55 @ 
% 39.73/39.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ X56)))
% 39.73/39.99          | ~ (v1_funct_1 @ X55)
% 39.73/39.99          | ~ (v1_relat_1 @ X55))),
% 39.73/39.99      inference('cnf', [status(esa)], [t4_funct_2])).
% 39.73/39.99  thf('230', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99             (k1_zfmisc_1 @ 
% 39.73/39.99              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 39.73/39.99      inference('sup-', [status(thm)], ['228', '229'])).
% 39.73/39.99  thf('231', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['173', '174'])).
% 39.73/39.99  thf('232', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 39.73/39.99          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99             (k1_zfmisc_1 @ 
% 39.73/39.99              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 39.73/39.99      inference('demod', [status(thm)], ['230', '231'])).
% 39.73/39.99  thf('233', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 39.73/39.99      inference('demod', [status(thm)], ['214', '215', '216'])).
% 39.73/39.99  thf('234', plain,
% 39.73/39.99      (![X0 : $i]:
% 39.73/39.99         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 39.73/39.99          (k1_zfmisc_1 @ 
% 39.73/39.99           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 39.73/39.99      inference('demod', [status(thm)], ['232', '233'])).
% 39.73/39.99  thf('235', plain,
% 39.73/39.99      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 39.73/39.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 39.73/39.99      inference('sup+', [status(thm)], ['227', '234'])).
% 39.73/39.99  thf('236', plain, ($false), inference('demod', [status(thm)], ['226', '235'])).
% 39.73/39.99  
% 39.73/39.99  % SZS output end Refutation
% 39.73/39.99  
% 39.73/39.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
