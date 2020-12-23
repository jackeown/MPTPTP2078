%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4ad9JVw56b

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:34 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  261 (2117 expanded)
%              Number of leaves         :   54 ( 661 expanded)
%              Depth                    :   22
%              Number of atoms          : 1928 (33334 expanded)
%              Number of equality atoms :  141 (1207 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('16',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('30',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('44',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['28','35','41','47'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('49',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_partfun1 @ X33 @ X34 )
      | ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('55',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('57',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('61',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['58'])).

thf('65',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf('70',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('71',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['58'])).

thf('75',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['68','73','74'])).

thf('76',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['61','75'])).

thf('77',plain,(
    ~ ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ sk_B ) ),
    inference(clc,[status(thm)],['57','76'])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('79',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('80',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['23','24'])).

thf('86',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('88',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['28','35','41','47'])).

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

thf('89',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X45 @ X46 )
      | ( zip_tseitin_1 @ X45 @ X47 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( zip_tseitin_0 @ X48 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('92',plain,(
    ! [X39: $i] :
      ( ( v1_funct_2 @ X39 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('95',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('96',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('97',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C ) @ X0 @ sk_B )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['90','97','98'])).

thf('100',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','99'])).

thf('101',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v1_funct_2 @ X40 @ X42 @ X41 )
      | ~ ( zip_tseitin_0 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('102',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['61','75'])).

thf('104',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','106'])).

thf('108',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ~ ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','108'])).

thf('110',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('111',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('112',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('113',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('114',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('115',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('116',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('117',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('118',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['115','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['114','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['113','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('130',plain,(
    ! [X3: $i] :
      ( ( ( k1_relat_1 @ X3 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('134',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','135'])).

thf('137',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('138',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('139',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('145',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('146',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('150',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('151',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('152',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','143','144','145','146','147','148','149','150','151'])).

thf('153',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['104','105'])).

thf('154',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['154'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('156',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('157',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('158',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['156','157'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('159',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('160',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('161',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['158','161'])).

thf('163',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('164',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['156','157'])).

thf('166',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('167',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('168',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['165','168'])).

thf('170',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['156','157'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('171',plain,(
    ! [X19: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X19 ) )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('172',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('173',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('174',plain,(
    ! [X19: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X19 ) )
      = ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['170','174'])).

thf('176',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['156','157'])).

thf('177',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['164','169','177'])).

thf('179',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['156','157'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('180',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('181',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('182',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['179','182'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('184',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('185',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('186',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('187',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X14 @ X13 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('188',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('189',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k5_relat_1 @ X14 @ X13 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('192',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( k1_xboole_0
     != ( k6_partfun1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['183','194'])).

thf('196',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['156','157'])).

thf('197',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['158','161'])).

thf('198',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['165','168'])).

thf('199',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['178','200'])).

thf('202',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['156','157'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('203',plain,(
    ! [X36: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X36 ) @ X36 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('204',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    $false ),
    inference(demod,[status(thm)],['109','155','201','204'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4ad9JVw56b
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.68  % Solved by: fo/fo7.sh
% 0.50/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.68  % done 575 iterations in 0.228s
% 0.50/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.68  % SZS output start Refutation
% 0.50/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.68  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.50/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.50/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.50/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.50/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.50/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.50/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.50/0.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.50/0.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.50/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.68  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.50/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.50/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.50/0.68  thf(t31_funct_2, conjecture,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.68       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.50/0.68         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.50/0.68           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.50/0.68           ( m1_subset_1 @
% 0.50/0.68             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.50/0.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.68          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.50/0.68            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.50/0.68              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.50/0.68              ( m1_subset_1 @
% 0.50/0.68                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.50/0.68    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.50/0.68  thf('0', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(cc2_relset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.50/0.68  thf('1', plain,
% 0.50/0.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.50/0.68         ((v4_relat_1 @ X23 @ X24)
% 0.50/0.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.50/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.68  thf('2', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.50/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.68  thf(d18_relat_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( v1_relat_1 @ B ) =>
% 0.50/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.50/0.68  thf('3', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (~ (v4_relat_1 @ X0 @ X1)
% 0.50/0.68          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.50/0.68          | ~ (v1_relat_1 @ X0))),
% 0.50/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.50/0.68  thf('4', plain,
% 0.50/0.68      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.68  thf('5', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(cc1_relset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.68       ( v1_relat_1 @ C ) ))).
% 0.50/0.68  thf('6', plain,
% 0.50/0.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.50/0.68         ((v1_relat_1 @ X20)
% 0.50/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.50/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.68  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('8', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.50/0.68      inference('demod', [status(thm)], ['4', '7'])).
% 0.50/0.68  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf(d9_funct_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.68       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.50/0.68  thf('10', plain,
% 0.50/0.68      (![X9 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X9)
% 0.50/0.68          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 0.50/0.68          | ~ (v1_funct_1 @ X9)
% 0.50/0.68          | ~ (v1_relat_1 @ X9))),
% 0.50/0.68      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.50/0.68  thf('11', plain,
% 0.50/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.68        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.50/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.68  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('13', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('14', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf(t55_funct_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.68       ( ( v2_funct_1 @ A ) =>
% 0.50/0.68         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.50/0.68           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.50/0.68  thf('15', plain,
% 0.50/0.68      (![X15 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X15)
% 0.50/0.68          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 0.50/0.68          | ~ (v1_funct_1 @ X15)
% 0.50/0.68          | ~ (v1_relat_1 @ X15))),
% 0.50/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.50/0.68  thf('16', plain,
% 0.50/0.68      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.50/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.50/0.68  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('19', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('20', plain,
% 0.50/0.68      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.50/0.68  thf('21', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.50/0.68  thf('22', plain,
% 0.50/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.68         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.50/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.50/0.68  thf('23', plain,
% 0.50/0.68      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.50/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.68  thf('24', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('25', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.50/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.50/0.68  thf('26', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['20', '25'])).
% 0.50/0.68  thf(t3_funct_2, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.68       ( ( v1_funct_1 @ A ) & 
% 0.50/0.68         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.50/0.68         ( m1_subset_1 @
% 0.50/0.68           A @ 
% 0.50/0.68           ( k1_zfmisc_1 @
% 0.50/0.68             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.50/0.68  thf('27', plain,
% 0.50/0.68      (![X39 : $i]:
% 0.50/0.68         ((m1_subset_1 @ X39 @ 
% 0.50/0.68           (k1_zfmisc_1 @ 
% 0.50/0.68            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 0.50/0.68          | ~ (v1_funct_1 @ X39)
% 0.50/0.68          | ~ (v1_relat_1 @ X39))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.50/0.68  thf('28', plain,
% 0.50/0.68      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.50/0.68         (k1_zfmisc_1 @ 
% 0.50/0.68          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))))
% 0.50/0.68        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.50/0.68        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.50/0.68  thf('29', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf('30', plain,
% 0.50/0.68      (![X15 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X15)
% 0.50/0.68          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 0.50/0.68          | ~ (v1_funct_1 @ X15)
% 0.50/0.68          | ~ (v1_relat_1 @ X15))),
% 0.50/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.50/0.68  thf('31', plain,
% 0.50/0.68      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.50/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.68      inference('sup+', [status(thm)], ['29', '30'])).
% 0.50/0.68  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('34', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('35', plain,
% 0.50/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.50/0.68  thf('36', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf(dt_k2_funct_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.68       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.50/0.68         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.50/0.68  thf('37', plain,
% 0.50/0.68      (![X10 : $i]:
% 0.50/0.68         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.50/0.68          | ~ (v1_funct_1 @ X10)
% 0.50/0.68          | ~ (v1_relat_1 @ X10))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.68  thf('38', plain,
% 0.50/0.68      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.50/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.68        | ~ (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('sup+', [status(thm)], ['36', '37'])).
% 0.50/0.68  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('41', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.50/0.68  thf('42', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf('43', plain,
% 0.50/0.68      (![X10 : $i]:
% 0.50/0.68         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.50/0.68          | ~ (v1_funct_1 @ X10)
% 0.50/0.68          | ~ (v1_relat_1 @ X10))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.68  thf('44', plain,
% 0.50/0.68      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.50/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.68        | ~ (v1_funct_1 @ sk_C))),
% 0.50/0.68      inference('sup+', [status(thm)], ['42', '43'])).
% 0.50/0.68  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('47', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.50/0.68  thf('48', plain,
% 0.50/0.68      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.50/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 0.50/0.68      inference('demod', [status(thm)], ['28', '35', '41', '47'])).
% 0.50/0.68  thf(t14_relset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.50/0.68       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.50/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.50/0.68  thf('49', plain,
% 0.50/0.68      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.50/0.68         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 0.50/0.68          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.50/0.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.50/0.68      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.50/0.68  thf('50', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.50/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.50/0.68          | ~ (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.50/0.68  thf('51', plain,
% 0.50/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.50/0.68  thf('52', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.50/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.50/0.68          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['50', '51'])).
% 0.50/0.68  thf('53', plain,
% 0.50/0.68      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.50/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['8', '52'])).
% 0.50/0.68  thf(cc1_funct_2, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.68       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.50/0.68         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.50/0.68  thf('54', plain,
% 0.50/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.50/0.68         (~ (v1_funct_1 @ X33)
% 0.50/0.68          | ~ (v1_partfun1 @ X33 @ X34)
% 0.50/0.68          | (v1_funct_2 @ X33 @ X34 @ X35)
% 0.50/0.68          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.50/0.68      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.50/0.68  thf('55', plain,
% 0.50/0.68      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.50/0.68        | ~ (v1_partfun1 @ (k4_relat_1 @ sk_C) @ sk_B)
% 0.50/0.68        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.50/0.68  thf('56', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.50/0.68  thf('57', plain,
% 0.50/0.68      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.50/0.68        | ~ (v1_partfun1 @ (k4_relat_1 @ sk_C) @ sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['55', '56'])).
% 0.50/0.68  thf('58', plain,
% 0.50/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.50/0.68        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('59', plain,
% 0.50/0.68      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.50/0.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.50/0.68      inference('split', [status(esa)], ['58'])).
% 0.50/0.68  thf('60', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf('61', plain,
% 0.50/0.68      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.50/0.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.50/0.68      inference('demod', [status(thm)], ['59', '60'])).
% 0.50/0.68  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('63', plain,
% 0.50/0.68      (![X10 : $i]:
% 0.50/0.68         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.50/0.68          | ~ (v1_funct_1 @ X10)
% 0.50/0.68          | ~ (v1_relat_1 @ X10))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.68  thf('64', plain,
% 0.50/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.68      inference('split', [status(esa)], ['58'])).
% 0.50/0.68  thf('65', plain,
% 0.50/0.68      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.50/0.68         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['63', '64'])).
% 0.50/0.68  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('67', plain,
% 0.50/0.68      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.50/0.68      inference('demod', [status(thm)], ['65', '66'])).
% 0.50/0.68  thf('68', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['62', '67'])).
% 0.50/0.68  thf('69', plain,
% 0.50/0.68      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.50/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['8', '52'])).
% 0.50/0.68  thf('70', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf('71', plain,
% 0.50/0.68      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.50/0.68         <= (~
% 0.50/0.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.50/0.68      inference('split', [status(esa)], ['58'])).
% 0.50/0.68  thf('72', plain,
% 0.50/0.68      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.50/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.50/0.68         <= (~
% 0.50/0.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['70', '71'])).
% 0.50/0.68  thf('73', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['69', '72'])).
% 0.50/0.68  thf('74', plain,
% 0.50/0.68      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.50/0.68       ~
% 0.50/0.68       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.50/0.68       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.68      inference('split', [status(esa)], ['58'])).
% 0.50/0.68  thf('75', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.50/0.68      inference('sat_resolution*', [status(thm)], ['68', '73', '74'])).
% 0.50/0.68  thf('76', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.50/0.68      inference('simpl_trail', [status(thm)], ['61', '75'])).
% 0.50/0.68  thf('77', plain, (~ (v1_partfun1 @ (k4_relat_1 @ sk_C) @ sk_B)),
% 0.50/0.68      inference('clc', [status(thm)], ['57', '76'])).
% 0.50/0.68  thf('78', plain,
% 0.50/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.50/0.68  thf(t65_relat_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( v1_relat_1 @ A ) =>
% 0.50/0.68       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.50/0.68         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.68  thf('79', plain,
% 0.50/0.68      (![X5 : $i]:
% 0.50/0.68         (((k2_relat_1 @ X5) != (k1_xboole_0))
% 0.50/0.68          | ((k1_relat_1 @ X5) = (k1_xboole_0))
% 0.50/0.68          | ~ (v1_relat_1 @ X5))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.50/0.68  thf('80', plain,
% 0.50/0.68      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))
% 0.50/0.68        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.50/0.68        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['78', '79'])).
% 0.50/0.68  thf('81', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.50/0.68  thf('82', plain,
% 0.50/0.68      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))
% 0.50/0.68        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['80', '81'])).
% 0.50/0.68  thf('83', plain,
% 0.50/0.68      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.50/0.68  thf('84', plain,
% 0.50/0.68      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))
% 0.50/0.68        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['82', '83'])).
% 0.50/0.68  thf('85', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.50/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.50/0.68  thf('86', plain,
% 0.50/0.68      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['84', '85'])).
% 0.50/0.68  thf('87', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.50/0.68      inference('demod', [status(thm)], ['4', '7'])).
% 0.50/0.68  thf('88', plain,
% 0.50/0.68      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.50/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 0.50/0.68      inference('demod', [status(thm)], ['28', '35', '41', '47'])).
% 0.50/0.68  thf(t9_funct_2, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.50/0.68         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.50/0.68       ( ( r1_tarski @ B @ C ) =>
% 0.50/0.68         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.50/0.68             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.50/0.68           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.50/0.68  thf(zf_stmt_2, axiom,
% 0.50/0.68    (![B:$i,A:$i]:
% 0.50/0.68     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.50/0.68       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.50/0.68  thf(zf_stmt_4, axiom,
% 0.50/0.68    (![D:$i,C:$i,A:$i]:
% 0.50/0.68     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.50/0.68       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.50/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_5, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.68       ( ( r1_tarski @ B @ C ) =>
% 0.50/0.68         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.50/0.68  thf('89', plain,
% 0.50/0.68      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.50/0.68         (~ (r1_tarski @ X45 @ X46)
% 0.50/0.68          | (zip_tseitin_1 @ X45 @ X47)
% 0.50/0.68          | ~ (v1_funct_1 @ X48)
% 0.50/0.68          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 0.50/0.68          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.50/0.68          | (zip_tseitin_0 @ X48 @ X46 @ X47))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.68  thf('90', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((zip_tseitin_0 @ (k4_relat_1 @ sk_C) @ X0 @ sk_B)
% 0.50/0.68          | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 0.50/0.68          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.50/0.68          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.50/0.68          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['88', '89'])).
% 0.50/0.68  thf('91', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['20', '25'])).
% 0.50/0.68  thf('92', plain,
% 0.50/0.68      (![X39 : $i]:
% 0.50/0.68         ((v1_funct_2 @ X39 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))
% 0.50/0.68          | ~ (v1_funct_1 @ X39)
% 0.50/0.68          | ~ (v1_relat_1 @ X39))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.50/0.68  thf('93', plain,
% 0.50/0.68      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ 
% 0.50/0.68         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.50/0.68        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.50/0.68        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['91', '92'])).
% 0.50/0.68  thf('94', plain,
% 0.50/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.50/0.68  thf('95', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.50/0.68  thf('96', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.50/0.68  thf('97', plain,
% 0.50/0.68      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.50/0.68  thf('98', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.50/0.68  thf('99', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((zip_tseitin_0 @ (k4_relat_1 @ sk_C) @ X0 @ sk_B)
% 0.50/0.68          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.50/0.68          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['90', '97', '98'])).
% 0.50/0.68  thf('100', plain,
% 0.50/0.68      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.50/0.68        | (zip_tseitin_0 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['87', '99'])).
% 0.50/0.68  thf('101', plain,
% 0.50/0.68      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.50/0.68         ((v1_funct_2 @ X40 @ X42 @ X41) | ~ (zip_tseitin_0 @ X40 @ X41 @ X42))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.50/0.68  thf('102', plain,
% 0.50/0.68      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.50/0.68        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['100', '101'])).
% 0.50/0.68  thf('103', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.50/0.68      inference('simpl_trail', [status(thm)], ['61', '75'])).
% 0.50/0.68  thf('104', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.50/0.68      inference('clc', [status(thm)], ['102', '103'])).
% 0.50/0.68  thf('105', plain,
% 0.50/0.68      (![X43 : $i, X44 : $i]:
% 0.50/0.68         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.68  thf('106', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['104', '105'])).
% 0.50/0.68  thf('107', plain,
% 0.50/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['86', '106'])).
% 0.50/0.68  thf('108', plain, (((sk_B) = (k1_xboole_0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['107'])).
% 0.50/0.68  thf('109', plain, (~ (v1_partfun1 @ (k4_relat_1 @ sk_C) @ k1_xboole_0)),
% 0.50/0.68      inference('demod', [status(thm)], ['77', '108'])).
% 0.50/0.68  thf('110', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf(t65_funct_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.68       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.50/0.68  thf('111', plain,
% 0.50/0.68      (![X18 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X18)
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X18)) = (X18))
% 0.50/0.68          | ~ (v1_funct_1 @ X18)
% 0.50/0.68          | ~ (v1_relat_1 @ X18))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.68  thf('112', plain,
% 0.50/0.68      (![X18 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X18)
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X18)) = (X18))
% 0.50/0.68          | ~ (v1_funct_1 @ X18)
% 0.50/0.68          | ~ (v1_relat_1 @ X18))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.68  thf('113', plain,
% 0.50/0.68      (![X10 : $i]:
% 0.50/0.68         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.50/0.68          | ~ (v1_funct_1 @ X10)
% 0.50/0.68          | ~ (v1_relat_1 @ X10))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.68  thf('114', plain,
% 0.50/0.68      (![X10 : $i]:
% 0.50/0.68         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.50/0.68          | ~ (v1_funct_1 @ X10)
% 0.50/0.68          | ~ (v1_relat_1 @ X10))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.68  thf('115', plain,
% 0.50/0.68      (![X18 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X18)
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X18)) = (X18))
% 0.50/0.68          | ~ (v1_funct_1 @ X18)
% 0.50/0.68          | ~ (v1_relat_1 @ X18))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.68  thf('116', plain,
% 0.50/0.68      (![X10 : $i]:
% 0.50/0.68         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.50/0.68          | ~ (v1_funct_1 @ X10)
% 0.50/0.68          | ~ (v1_relat_1 @ X10))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.68  thf('117', plain,
% 0.50/0.68      (![X10 : $i]:
% 0.50/0.68         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.50/0.68          | ~ (v1_funct_1 @ X10)
% 0.50/0.68          | ~ (v1_relat_1 @ X10))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.50/0.68  thf('118', plain,
% 0.50/0.68      (![X9 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X9)
% 0.50/0.68          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 0.50/0.68          | ~ (v1_funct_1 @ X9)
% 0.50/0.68          | ~ (v1_relat_1 @ X9))),
% 0.50/0.68      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.50/0.68  thf('119', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.68              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['117', '118'])).
% 0.50/0.68  thf('120', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.68              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['116', '119'])).
% 0.50/0.68  thf('121', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['120'])).
% 0.50/0.68  thf('122', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['115', '121'])).
% 0.50/0.68  thf('123', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.50/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['122'])).
% 0.50/0.68  thf('124', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['114', '123'])).
% 0.50/0.68  thf('125', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.50/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['124'])).
% 0.50/0.68  thf('126', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['113', '125'])).
% 0.50/0.68  thf('127', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['126'])).
% 0.50/0.68  thf('128', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k2_funct_1 @ X0) = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['112', '127'])).
% 0.50/0.68  thf('129', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ((k2_funct_1 @ X0)
% 0.50/0.68              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.50/0.68      inference('simplify', [status(thm)], ['128'])).
% 0.50/0.68  thf(t37_relat_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( v1_relat_1 @ A ) =>
% 0.50/0.68       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.50/0.68         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.50/0.68  thf('130', plain,
% 0.50/0.68      (![X3 : $i]:
% 0.50/0.68         (((k1_relat_1 @ X3) = (k2_relat_1 @ (k4_relat_1 @ X3)))
% 0.50/0.68          | ~ (v1_relat_1 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.50/0.68  thf('131', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['129', '130'])).
% 0.50/0.68  thf('132', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['111', '131'])).
% 0.50/0.68  thf('133', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['132'])).
% 0.50/0.68  thf(t64_relat_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( v1_relat_1 @ A ) =>
% 0.50/0.68       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.68           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.68         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.68  thf('134', plain,
% 0.50/0.68      (![X4 : $i]:
% 0.50/0.68         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 0.50/0.68          | ((X4) = (k1_xboole_0))
% 0.50/0.68          | ~ (v1_relat_1 @ X4))),
% 0.50/0.68      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.50/0.68  thf('135', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_xboole_0))
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['133', '134'])).
% 0.50/0.68  thf('136', plain,
% 0.50/0.68      ((~ (v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.50/0.68        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 0.50/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.50/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_xboole_0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['110', '135'])).
% 0.50/0.68  thf('137', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf('138', plain,
% 0.50/0.68      (![X18 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X18)
% 0.50/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X18)) = (X18))
% 0.50/0.68          | ~ (v1_funct_1 @ X18)
% 0.50/0.68          | ~ (v1_relat_1 @ X18))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.50/0.68  thf('139', plain,
% 0.50/0.68      ((((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))
% 0.50/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.50/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.50/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.68      inference('sup+', [status(thm)], ['137', '138'])).
% 0.50/0.68  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('143', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.50/0.68  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('145', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf('146', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.50/0.68  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('150', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.50/0.68      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.50/0.68  thf('151', plain,
% 0.50/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.50/0.68      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.50/0.68  thf('152', plain,
% 0.50/0.68      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.50/0.68      inference('demod', [status(thm)],
% 0.50/0.68                ['136', '143', '144', '145', '146', '147', '148', '149', 
% 0.50/0.68                 '150', '151'])).
% 0.50/0.68  thf('153', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['104', '105'])).
% 0.50/0.68  thf('154', plain,
% 0.50/0.68      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['152', '153'])).
% 0.50/0.68  thf('155', plain, (((sk_C) = (k1_xboole_0))),
% 0.50/0.68      inference('simplify', [status(thm)], ['154'])).
% 0.50/0.68  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.50/0.68  thf('156', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.50/0.68  thf(redefinition_k6_partfun1, axiom,
% 0.50/0.68    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.50/0.68  thf('157', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.68  thf('158', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['156', '157'])).
% 0.50/0.68  thf(fc3_funct_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.50/0.68       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.50/0.68  thf('159', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.50/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.50/0.68  thf('160', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.68  thf('161', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 0.50/0.68      inference('demod', [status(thm)], ['159', '160'])).
% 0.50/0.68  thf('162', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.50/0.68      inference('sup+', [status(thm)], ['158', '161'])).
% 0.50/0.68  thf('163', plain,
% 0.50/0.68      (![X9 : $i]:
% 0.50/0.68         (~ (v2_funct_1 @ X9)
% 0.50/0.68          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 0.50/0.68          | ~ (v1_funct_1 @ X9)
% 0.50/0.68          | ~ (v1_relat_1 @ X9))),
% 0.50/0.68      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.50/0.68  thf('164', plain,
% 0.50/0.68      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.50/0.68        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.50/0.68        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['162', '163'])).
% 0.50/0.68  thf('165', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['156', '157'])).
% 0.50/0.68  thf('166', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 0.50/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.50/0.68  thf('167', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.68  thf('168', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 0.50/0.68      inference('demod', [status(thm)], ['166', '167'])).
% 0.50/0.68  thf('169', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.50/0.68      inference('sup+', [status(thm)], ['165', '168'])).
% 0.50/0.68  thf('170', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['156', '157'])).
% 0.50/0.68  thf(t67_funct_1, axiom,
% 0.50/0.68    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.50/0.68  thf('171', plain,
% 0.50/0.68      (![X19 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X19)) = (k6_relat_1 @ X19))),
% 0.50/0.68      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.50/0.68  thf('172', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.68  thf('173', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.68  thf('174', plain,
% 0.50/0.68      (![X19 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X19)) = (k6_partfun1 @ X19))),
% 0.50/0.68      inference('demod', [status(thm)], ['171', '172', '173'])).
% 0.50/0.68  thf('175', plain,
% 0.50/0.68      (((k2_funct_1 @ k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['170', '174'])).
% 0.50/0.68  thf('176', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['156', '157'])).
% 0.50/0.68  thf('177', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['175', '176'])).
% 0.50/0.68  thf('178', plain,
% 0.50/0.68      ((((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.50/0.68        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['164', '169', '177'])).
% 0.50/0.68  thf('179', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['156', '157'])).
% 0.50/0.68  thf(t71_relat_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.50/0.68       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.50/0.68  thf('180', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.50/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.50/0.68  thf('181', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.68  thf('182', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 0.50/0.68      inference('demod', [status(thm)], ['180', '181'])).
% 0.50/0.68  thf('183', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['179', '182'])).
% 0.50/0.68  thf(t80_relat_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( v1_relat_1 @ A ) =>
% 0.50/0.68       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.50/0.68  thf('184', plain,
% 0.50/0.68      (![X8 : $i]:
% 0.50/0.68         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 0.50/0.68          | ~ (v1_relat_1 @ X8))),
% 0.50/0.68      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.50/0.68  thf('185', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.68  thf('186', plain,
% 0.50/0.68      (![X8 : $i]:
% 0.50/0.68         (((k5_relat_1 @ X8 @ (k6_partfun1 @ (k2_relat_1 @ X8))) = (X8))
% 0.50/0.68          | ~ (v1_relat_1 @ X8))),
% 0.50/0.68      inference('demod', [status(thm)], ['184', '185'])).
% 0.50/0.68  thf(t53_funct_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.68       ( ( ?[B:$i]:
% 0.50/0.68           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.50/0.68             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.50/0.68         ( v2_funct_1 @ A ) ) ))).
% 0.50/0.68  thf('187', plain,
% 0.50/0.68      (![X13 : $i, X14 : $i]:
% 0.50/0.68         (~ (v1_relat_1 @ X13)
% 0.50/0.68          | ~ (v1_funct_1 @ X13)
% 0.50/0.68          | ((k5_relat_1 @ X14 @ X13) != (k6_relat_1 @ (k1_relat_1 @ X14)))
% 0.50/0.68          | (v2_funct_1 @ X14)
% 0.50/0.68          | ~ (v1_funct_1 @ X14)
% 0.50/0.68          | ~ (v1_relat_1 @ X14))),
% 0.50/0.68      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.50/0.68  thf('188', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.50/0.68  thf('189', plain,
% 0.50/0.68      (![X13 : $i, X14 : $i]:
% 0.50/0.68         (~ (v1_relat_1 @ X13)
% 0.50/0.68          | ~ (v1_funct_1 @ X13)
% 0.50/0.68          | ((k5_relat_1 @ X14 @ X13) != (k6_partfun1 @ (k1_relat_1 @ X14)))
% 0.50/0.68          | (v2_funct_1 @ X14)
% 0.50/0.68          | ~ (v1_funct_1 @ X14)
% 0.50/0.68          | ~ (v1_relat_1 @ X14))),
% 0.50/0.68      inference('demod', [status(thm)], ['187', '188'])).
% 0.50/0.68  thf('190', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((X0) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | (v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 0.50/0.68          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['186', '189'])).
% 0.50/0.68  thf('191', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 0.50/0.68      inference('demod', [status(thm)], ['166', '167'])).
% 0.50/0.68  thf('192', plain, (![X11 : $i]: (v1_relat_1 @ (k6_partfun1 @ X11))),
% 0.50/0.68      inference('demod', [status(thm)], ['159', '160'])).
% 0.50/0.68  thf('193', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((X0) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | (v2_funct_1 @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['190', '191', '192'])).
% 0.50/0.68  thf('194', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((v2_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_funct_1 @ X0)
% 0.50/0.68          | ~ (v1_relat_1 @ X0)
% 0.50/0.68          | ((X0) != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 0.50/0.68      inference('simplify', [status(thm)], ['193'])).
% 0.50/0.68  thf('195', plain,
% 0.50/0.68      ((((k1_xboole_0) != (k6_partfun1 @ k1_xboole_0))
% 0.50/0.68        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.50/0.68        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.50/0.68        | (v2_funct_1 @ k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['183', '194'])).
% 0.50/0.68  thf('196', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['156', '157'])).
% 0.50/0.68  thf('197', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.50/0.68      inference('sup+', [status(thm)], ['158', '161'])).
% 0.50/0.68  thf('198', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.50/0.68      inference('sup+', [status(thm)], ['165', '168'])).
% 0.50/0.68  thf('199', plain,
% 0.50/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_funct_1 @ k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 0.50/0.68  thf('200', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.50/0.68      inference('simplify', [status(thm)], ['199'])).
% 0.50/0.68  thf('201', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['178', '200'])).
% 0.50/0.68  thf('202', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['156', '157'])).
% 0.50/0.68  thf(dt_k6_partfun1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( m1_subset_1 @
% 0.50/0.68         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.50/0.68       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.50/0.68  thf('203', plain, (![X36 : $i]: (v1_partfun1 @ (k6_partfun1 @ X36) @ X36)),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.50/0.68  thf('204', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.50/0.68      inference('sup+', [status(thm)], ['202', '203'])).
% 0.50/0.68  thf('205', plain, ($false),
% 0.50/0.68      inference('demod', [status(thm)], ['109', '155', '201', '204'])).
% 0.50/0.68  
% 0.50/0.68  % SZS output end Refutation
% 0.50/0.68  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
