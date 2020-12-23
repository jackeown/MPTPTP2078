%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NtfupBSegt

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:33 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  224 (7380 expanded)
%              Number of leaves         :   40 (2264 expanded)
%              Depth                    :   44
%              Number of atoms          : 1596 (116800 expanded)
%              Number of equality atoms :   87 (3588 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C @ sk_A_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('23',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['25','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B_1
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B_1
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X38: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf(t9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('75',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ X44 @ X45 )
      | ( zip_tseitin_1 @ X44 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( zip_tseitin_0 @ X47 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ X0 @ sk_B_1 )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('78',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('79',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('80',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58'])).

thf('81',plain,(
    ! [X38: $i] :
      ( ( v1_funct_2 @ X38 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('82',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ sk_A_1 @ sk_B_1 )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','100'])).

thf('102',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v1_funct_2 @ X39 @ X41 @ X40 )
      | ~ ( zip_tseitin_0 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('103',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('107',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('108',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('111',plain,(
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X20 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('112',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('115',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('119',plain,(
    ! [X42: $i] :
      ~ ( zip_tseitin_1 @ X42 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','120','121'])).

thf('123',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','122'])).

thf('124',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('125',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('126',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('127',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('128',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['125','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('134',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('137',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('138',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('141',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['124','141'])).

thf('143',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,(
    ! [X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X20 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('149',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('151',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58'])).

thf('152',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ sk_A_1 @ sk_B_1 )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','100'])).

thf('154',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( zip_tseitin_0 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('155',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','122'])).

thf('157',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['152','159'])).

thf('161',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['160'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('162',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('163',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['123','161','163'])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['157','158'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('166',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('167',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('169',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('172',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('173',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('175',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['157','158'])).

thf('177',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k2_funct_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['169'])).

thf('180',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['178','179'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('181',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['164','170','180','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NtfupBSegt
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.55/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.75  % Solved by: fo/fo7.sh
% 0.55/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.75  % done 667 iterations in 0.284s
% 0.55/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.75  % SZS output start Refutation
% 0.55/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.75  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.55/0.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.75  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.55/0.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.55/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.55/0.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.55/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.75  thf(t31_funct_2, conjecture,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.75       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.55/0.75         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.55/0.75           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.55/0.75           ( m1_subset_1 @
% 0.55/0.75             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.75            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.75          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.55/0.75            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.55/0.75              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.55/0.75              ( m1_subset_1 @
% 0.55/0.75                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.55/0.75    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.55/0.75  thf('0', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)
% 0.55/0.75        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('1', plain,
% 0.55/0.75      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1))))
% 0.55/0.75         <= (~
% 0.55/0.75             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))))),
% 0.55/0.75      inference('split', [status(esa)], ['0'])).
% 0.55/0.75  thf('2', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(cc1_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( v1_relat_1 @ C ) ))).
% 0.55/0.75  thf('3', plain,
% 0.55/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.75         ((v1_relat_1 @ X25)
% 0.55/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.75  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf(dt_k2_funct_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.75       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.55/0.75         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.55/0.75  thf('5', plain,
% 0.55/0.75      (![X23 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 0.55/0.75          | ~ (v1_funct_1 @ X23)
% 0.55/0.75          | ~ (v1_relat_1 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('6', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('split', [status(esa)], ['0'])).
% 0.55/0.75  thf('7', plain,
% 0.55/0.75      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.55/0.75         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.75  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('9', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.55/0.75  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['4', '9'])).
% 0.55/0.75  thf('11', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(cc2_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.75  thf('12', plain,
% 0.55/0.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.75         ((v4_relat_1 @ X28 @ X29)
% 0.55/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.75  thf('13', plain, ((v4_relat_1 @ sk_C @ sk_A_1)),
% 0.55/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.75  thf(d18_relat_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ B ) =>
% 0.55/0.75       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.55/0.75  thf('14', plain,
% 0.55/0.75      (![X13 : $i, X14 : $i]:
% 0.55/0.75         (~ (v4_relat_1 @ X13 @ X14)
% 0.55/0.75          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.55/0.75          | ~ (v1_relat_1 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.75  thf('15', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.75  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A_1)),
% 0.55/0.75      inference('demod', [status(thm)], ['15', '16'])).
% 0.55/0.75  thf('18', plain,
% 0.55/0.75      (![X23 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 0.55/0.75          | ~ (v1_funct_1 @ X23)
% 0.55/0.75          | ~ (v1_relat_1 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf(t55_funct_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.75       ( ( v2_funct_1 @ A ) =>
% 0.55/0.75         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.55/0.75           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.55/0.75  thf('19', plain,
% 0.55/0.75      (![X24 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X24)
% 0.55/0.75          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 0.55/0.75          | ~ (v1_funct_1 @ X24)
% 0.55/0.75          | ~ (v1_relat_1 @ X24))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('20', plain,
% 0.55/0.75      (![X23 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 0.55/0.75          | ~ (v1_funct_1 @ X23)
% 0.55/0.75          | ~ (v1_relat_1 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('21', plain,
% 0.55/0.75      (![X23 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.55/0.75          | ~ (v1_funct_1 @ X23)
% 0.55/0.75          | ~ (v1_relat_1 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('22', plain,
% 0.55/0.75      (![X24 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X24)
% 0.55/0.75          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 0.55/0.75          | ~ (v1_funct_1 @ X24)
% 0.55/0.75          | ~ (v1_relat_1 @ X24))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('23', plain,
% 0.55/0.75      (![X23 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.55/0.75          | ~ (v1_funct_1 @ X23)
% 0.55/0.75          | ~ (v1_relat_1 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf(d10_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.75  thf('24', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.55/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.75  thf('25', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.75      inference('simplify', [status(thm)], ['24'])).
% 0.55/0.75  thf('26', plain,
% 0.55/0.75      (![X23 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.55/0.75          | ~ (v1_funct_1 @ X23)
% 0.55/0.75          | ~ (v1_relat_1 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('27', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(redefinition_k2_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.55/0.75  thf('28', plain,
% 0.55/0.75      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.75         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.55/0.75          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.75  thf('29', plain,
% 0.55/0.75      (((k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.55/0.75  thf('30', plain, (((k2_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (sk_B_1))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('31', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['29', '30'])).
% 0.55/0.75  thf('32', plain,
% 0.55/0.75      (![X24 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X24)
% 0.55/0.75          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 0.55/0.75          | ~ (v1_funct_1 @ X24)
% 0.55/0.75          | ~ (v1_relat_1 @ X24))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('33', plain,
% 0.55/0.75      (![X13 : $i, X14 : $i]:
% 0.55/0.75         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.55/0.75          | (v4_relat_1 @ X13 @ X14)
% 0.55/0.75          | ~ (v1_relat_1 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.75  thf('34', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | (v4_relat_1 @ (k2_funct_1 @ X0) @ X1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.75  thf('35', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r1_tarski @ sk_B_1 @ X0)
% 0.55/0.75          | (v4_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75          | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75          | ~ (v1_relat_1 @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['31', '34'])).
% 0.55/0.75  thf('36', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r1_tarski @ sk_B_1 @ X0)
% 0.55/0.75          | (v4_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.55/0.75  thf('40', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ sk_C)
% 0.55/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75          | (v4_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.55/0.75          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['26', '39'])).
% 0.55/0.75  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('43', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.55/0.75  thf('44', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B_1)),
% 0.55/0.75      inference('sup-', [status(thm)], ['25', '43'])).
% 0.55/0.75  thf('45', plain,
% 0.55/0.75      (![X13 : $i, X14 : $i]:
% 0.55/0.75         (~ (v4_relat_1 @ X13 @ X14)
% 0.55/0.75          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.55/0.75          | ~ (v1_relat_1 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.75  thf('46', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['44', '45'])).
% 0.55/0.75  thf('47', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['23', '46'])).
% 0.55/0.75  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('50', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B_1)),
% 0.55/0.75      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.55/0.75  thf('51', plain,
% 0.55/0.75      (![X0 : $i, X2 : $i]:
% 0.55/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.75  thf('52', plain,
% 0.55/0.75      ((~ (r1_tarski @ sk_B_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75        | ((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.75  thf('53', plain,
% 0.55/0.75      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75        | ((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['22', '52'])).
% 0.55/0.75  thf('54', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['29', '30'])).
% 0.55/0.75  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.75      inference('simplify', [status(thm)], ['24'])).
% 0.55/0.75  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('59', plain, (((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['53', '54', '55', '56', '57', '58'])).
% 0.55/0.75  thf(t3_funct_2, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.75       ( ( v1_funct_1 @ A ) & 
% 0.55/0.75         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.55/0.75         ( m1_subset_1 @
% 0.55/0.75           A @ 
% 0.55/0.75           ( k1_zfmisc_1 @
% 0.55/0.75             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.75  thf('60', plain,
% 0.55/0.75      (![X38 : $i]:
% 0.55/0.75         ((m1_subset_1 @ X38 @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38))))
% 0.55/0.75          | ~ (v1_funct_1 @ X38)
% 0.55/0.75          | ~ (v1_relat_1 @ X38))),
% 0.55/0.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.55/0.75  thf('61', plain,
% 0.55/0.75      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 0.55/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['59', '60'])).
% 0.55/0.75  thf('62', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['21', '61'])).
% 0.55/0.75  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('65', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 0.55/0.75      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.55/0.75  thf('66', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['20', '65'])).
% 0.55/0.75  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('69', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.55/0.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.55/0.75  thf('70', plain,
% 0.55/0.75      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C))))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup+', [status(thm)], ['19', '69'])).
% 0.55/0.75  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('74', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C))))),
% 0.55/0.75      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.55/0.75  thf(t9_funct_2, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.75         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.55/0.75       ( ( r1_tarski @ B @ C ) =>
% 0.55/0.75         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.55/0.75             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.55/0.75           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_2, axiom,
% 0.55/0.75    (![B:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.55/0.75       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.55/0.75  thf(zf_stmt_4, axiom,
% 0.55/0.75    (![D:$i,C:$i,A:$i]:
% 0.55/0.75     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.55/0.75       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.55/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_5, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.75       ( ( r1_tarski @ B @ C ) =>
% 0.55/0.75         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.55/0.75  thf('75', plain,
% 0.55/0.75      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.55/0.75         (~ (r1_tarski @ X44 @ X45)
% 0.55/0.75          | (zip_tseitin_1 @ X44 @ X46)
% 0.55/0.75          | ~ (v1_funct_1 @ X47)
% 0.55/0.75          | ~ (v1_funct_2 @ X47 @ X46 @ X44)
% 0.55/0.75          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.55/0.75          | (zip_tseitin_0 @ X47 @ X45 @ X46))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.55/0.75  thf('76', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ X0 @ sk_B_1)
% 0.55/0.75          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ (k1_relat_1 @ sk_C))
% 0.55/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)
% 0.55/0.75          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['74', '75'])).
% 0.55/0.75  thf('77', plain,
% 0.55/0.75      (![X24 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X24)
% 0.55/0.75          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 0.55/0.75          | ~ (v1_funct_1 @ X24)
% 0.55/0.75          | ~ (v1_relat_1 @ X24))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('78', plain,
% 0.55/0.75      (![X23 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 0.55/0.75          | ~ (v1_funct_1 @ X23)
% 0.55/0.75          | ~ (v1_relat_1 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('79', plain,
% 0.55/0.75      (![X23 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.55/0.75          | ~ (v1_funct_1 @ X23)
% 0.55/0.75          | ~ (v1_relat_1 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('80', plain, (((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['53', '54', '55', '56', '57', '58'])).
% 0.55/0.75  thf('81', plain,
% 0.55/0.75      (![X38 : $i]:
% 0.55/0.75         ((v1_funct_2 @ X38 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38))
% 0.55/0.75          | ~ (v1_funct_1 @ X38)
% 0.55/0.75          | ~ (v1_relat_1 @ X38))),
% 0.55/0.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.55/0.75  thf('82', plain,
% 0.55/0.75      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ 
% 0.55/0.75         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['80', '81'])).
% 0.55/0.75  thf('83', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ 
% 0.55/0.75           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['79', '82'])).
% 0.55/0.75  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('86', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ 
% 0.55/0.75           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.55/0.75  thf('87', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ 
% 0.55/0.75           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['78', '86'])).
% 0.55/0.75  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('90', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ 
% 0.55/0.75        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.55/0.75  thf('91', plain,
% 0.55/0.75      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ (k1_relat_1 @ sk_C))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup+', [status(thm)], ['77', '90'])).
% 0.55/0.75  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('95', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ (k1_relat_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.55/0.75  thf('96', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ X0 @ sk_B_1)
% 0.55/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)
% 0.55/0.75          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['76', '95'])).
% 0.55/0.75  thf('97', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ sk_C)
% 0.55/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.55/0.75          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)
% 0.55/0.75          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ X0 @ sk_B_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['18', '96'])).
% 0.55/0.75  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('100', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.55/0.75          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)
% 0.55/0.75          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ X0 @ sk_B_1))),
% 0.55/0.75      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.55/0.75  thf('101', plain,
% 0.55/0.75      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ sk_A_1 @ sk_B_1)
% 0.55/0.75        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['17', '100'])).
% 0.55/0.75  thf('102', plain,
% 0.55/0.75      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.55/0.75         ((v1_funct_2 @ X39 @ X41 @ X40) | ~ (zip_tseitin_0 @ X39 @ X40 @ X41))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.55/0.75  thf('103', plain,
% 0.55/0.75      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)
% 0.55/0.75        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['101', '102'])).
% 0.55/0.75  thf('104', plain,
% 0.55/0.75      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('split', [status(esa)], ['0'])).
% 0.55/0.75  thf('105', plain,
% 0.55/0.75      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['103', '104'])).
% 0.55/0.75  thf('106', plain,
% 0.55/0.75      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['103', '104'])).
% 0.55/0.75  thf('107', plain,
% 0.55/0.75      (![X42 : $i, X43 : $i]:
% 0.55/0.75         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.75  thf('108', plain,
% 0.55/0.75      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['106', '107'])).
% 0.55/0.75  thf('109', plain,
% 0.55/0.75      (((zip_tseitin_1 @ k1_xboole_0 @ sk_B_1))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('demod', [status(thm)], ['105', '108'])).
% 0.55/0.75  thf('110', plain,
% 0.55/0.75      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['106', '107'])).
% 0.55/0.75  thf(t65_relat_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ A ) =>
% 0.55/0.75       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.55/0.75         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.75  thf('111', plain,
% 0.55/0.75      (![X20 : $i]:
% 0.55/0.75         (((k1_relat_1 @ X20) != (k1_xboole_0))
% 0.55/0.75          | ((k2_relat_1 @ X20) = (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X20))),
% 0.55/0.75      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.55/0.75  thf('112', plain,
% 0.55/0.75      (((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.75         | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75         | ((k2_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['110', '111'])).
% 0.55/0.75  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('114', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['29', '30'])).
% 0.55/0.75  thf('115', plain,
% 0.55/0.75      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.55/0.75  thf('116', plain,
% 0.55/0.75      ((((sk_B_1) = (k1_xboole_0)))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['115'])).
% 0.55/0.75  thf('117', plain,
% 0.55/0.75      (((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.55/0.75         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('demod', [status(thm)], ['109', '116'])).
% 0.55/0.75  thf('118', plain,
% 0.55/0.75      (![X42 : $i, X43 : $i]:
% 0.55/0.75         (((X43) != (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.75  thf('119', plain, (![X42 : $i]: ~ (zip_tseitin_1 @ X42 @ k1_xboole_0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['118'])).
% 0.55/0.75  thf('120', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['117', '119'])).
% 0.55/0.75  thf('121', plain,
% 0.55/0.75      (~
% 0.55/0.75       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))) | 
% 0.55/0.75       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A_1)) | 
% 0.55/0.75       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('split', [status(esa)], ['0'])).
% 0.55/0.75  thf('122', plain,
% 0.55/0.75      (~
% 0.55/0.75       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1))))),
% 0.55/0.75      inference('sat_resolution*', [status(thm)], ['10', '120', '121'])).
% 0.55/0.75  thf('123', plain,
% 0.55/0.75      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('simpl_trail', [status(thm)], ['1', '122'])).
% 0.55/0.75  thf('124', plain,
% 0.55/0.75      (![X24 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X24)
% 0.55/0.75          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 0.55/0.75          | ~ (v1_funct_1 @ X24)
% 0.55/0.75          | ~ (v1_relat_1 @ X24))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('125', plain,
% 0.55/0.75      (![X24 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X24)
% 0.55/0.75          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 0.55/0.75          | ~ (v1_funct_1 @ X24)
% 0.55/0.75          | ~ (v1_relat_1 @ X24))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('126', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.55/0.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.55/0.75  thf('127', plain,
% 0.55/0.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.75         ((v5_relat_1 @ X28 @ X30)
% 0.55/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.75  thf('128', plain,
% 0.55/0.75      ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['126', '127'])).
% 0.55/0.75  thf('129', plain,
% 0.55/0.75      (((v5_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup+', [status(thm)], ['125', '128'])).
% 0.55/0.75  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('133', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 0.55/0.75  thf(d19_relat_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ B ) =>
% 0.55/0.75       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.55/0.75  thf('134', plain,
% 0.55/0.75      (![X15 : $i, X16 : $i]:
% 0.55/0.75         (~ (v5_relat_1 @ X15 @ X16)
% 0.55/0.75          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.55/0.75          | ~ (v1_relat_1 @ X15))),
% 0.55/0.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.55/0.75  thf('135', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['133', '134'])).
% 0.55/0.75  thf('136', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.55/0.75      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.55/0.75  thf('137', plain,
% 0.55/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.75         ((v1_relat_1 @ X25)
% 0.55/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.75  thf('138', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['136', '137'])).
% 0.55/0.75  thf('139', plain,
% 0.55/0.75      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['135', '138'])).
% 0.55/0.75  thf('140', plain,
% 0.55/0.75      (![X0 : $i, X2 : $i]:
% 0.55/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.55/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.75  thf('141', plain,
% 0.55/0.75      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['139', '140'])).
% 0.55/0.75  thf('142', plain,
% 0.55/0.75      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['124', '141'])).
% 0.55/0.75  thf('143', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.75      inference('simplify', [status(thm)], ['24'])).
% 0.55/0.75  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('147', plain,
% 0.55/0.75      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 0.55/0.75  thf('148', plain,
% 0.55/0.75      (![X20 : $i]:
% 0.55/0.75         (((k2_relat_1 @ X20) != (k1_xboole_0))
% 0.55/0.75          | ((k1_relat_1 @ X20) = (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X20))),
% 0.55/0.75      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.55/0.75  thf('149', plain,
% 0.55/0.75      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))
% 0.55/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['147', '148'])).
% 0.55/0.75  thf('150', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['136', '137'])).
% 0.55/0.75  thf('151', plain, (((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['53', '54', '55', '56', '57', '58'])).
% 0.55/0.75  thf('152', plain,
% 0.55/0.75      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.55/0.75  thf('153', plain,
% 0.55/0.75      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ sk_A_1 @ sk_B_1)
% 0.55/0.75        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['17', '100'])).
% 0.55/0.75  thf('154', plain,
% 0.55/0.75      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.55/0.75         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.55/0.75          | ~ (zip_tseitin_0 @ X39 @ X40 @ X41))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.55/0.75  thf('155', plain,
% 0.55/0.75      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)
% 0.55/0.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['153', '154'])).
% 0.55/0.75  thf('156', plain,
% 0.55/0.75      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))),
% 0.55/0.75      inference('simpl_trail', [status(thm)], ['1', '122'])).
% 0.55/0.75  thf('157', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)),
% 0.55/0.75      inference('clc', [status(thm)], ['155', '156'])).
% 0.55/0.75  thf('158', plain,
% 0.55/0.75      (![X42 : $i, X43 : $i]:
% 0.55/0.75         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.75  thf('159', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['157', '158'])).
% 0.55/0.75  thf('160', plain,
% 0.55/0.75      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['152', '159'])).
% 0.55/0.75  thf('161', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['160'])).
% 0.55/0.75  thf(t113_zfmisc_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.55/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.75  thf('162', plain,
% 0.55/0.75      (![X4 : $i, X5 : $i]:
% 0.55/0.75         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.75  thf('163', plain,
% 0.55/0.75      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['162'])).
% 0.55/0.75  thf('164', plain,
% 0.55/0.75      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.55/0.75      inference('demod', [status(thm)], ['123', '161', '163'])).
% 0.55/0.75  thf('165', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['157', '158'])).
% 0.55/0.75  thf(t64_relat_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ A ) =>
% 0.55/0.75       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.55/0.75           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.75         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.75  thf('166', plain,
% 0.55/0.75      (![X19 : $i]:
% 0.55/0.75         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.55/0.75          | ((X19) = (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X19))),
% 0.55/0.75      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.55/0.75  thf('167', plain,
% 0.55/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ((sk_C) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['165', '166'])).
% 0.55/0.75  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('169', plain,
% 0.55/0.75      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['167', '168'])).
% 0.55/0.75  thf('170', plain, (((sk_C) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['169'])).
% 0.55/0.75  thf('171', plain,
% 0.55/0.75      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 0.55/0.75  thf('172', plain,
% 0.55/0.75      (![X19 : $i]:
% 0.55/0.75         (((k2_relat_1 @ X19) != (k1_xboole_0))
% 0.55/0.75          | ((X19) = (k1_xboole_0))
% 0.55/0.75          | ~ (v1_relat_1 @ X19))),
% 0.55/0.75      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.55/0.75  thf('173', plain,
% 0.55/0.75      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))
% 0.55/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['171', '172'])).
% 0.55/0.75  thf('174', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['136', '137'])).
% 0.55/0.75  thf('175', plain,
% 0.55/0.75      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))
% 0.55/0.75        | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['173', '174'])).
% 0.55/0.75  thf('176', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['157', '158'])).
% 0.55/0.75  thf('177', plain,
% 0.55/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.55/0.75        | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['175', '176'])).
% 0.55/0.75  thf('178', plain, (((k2_funct_1 @ sk_C) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['177'])).
% 0.55/0.75  thf('179', plain, (((sk_C) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['169'])).
% 0.55/0.75  thf('180', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.75      inference('demod', [status(thm)], ['178', '179'])).
% 0.55/0.75  thf(t4_subset_1, axiom,
% 0.55/0.75    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.55/0.75  thf('181', plain,
% 0.55/0.75      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.55/0.75      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.55/0.75  thf('182', plain, ($false),
% 0.55/0.75      inference('demod', [status(thm)], ['164', '170', '180', '181'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
