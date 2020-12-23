%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eE2ySn6zUi

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:14 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  243 (1296 expanded)
%              Number of leaves         :   48 ( 416 expanded)
%              Depth                    :   34
%              Number of atoms          : 1917 (24806 expanded)
%              Number of equality atoms :  119 (1619 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ X25 @ ( k2_funct_1 @ X25 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ X25 @ ( k2_funct_1 @ X25 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('6',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('9',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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

thf('10',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('11',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['26','31','32','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('50',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('51',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('60',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('61',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('62',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['7','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('74',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('75',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('76',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('85',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','80','81','82','83','84'])).

thf('86',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','93'])).

thf('95',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['0','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('106',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('115',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('122',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','123'])).

thf('125',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('126',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['110','111','126'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('128',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('129',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('132',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('136',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['129','130','131','136'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('138',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X9 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('139',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('143',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('144',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('146',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('148',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['129','130','131','136'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('151',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['141','148','149','150'])).

thf('152',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','151'])).

thf('153',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['110','111','126'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('155',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['134','135'])).

thf('157',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('160',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['134','135'])).

thf('164',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('166',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k2_relat_1 @ X23 ) )
      | ( ( k9_relat_1 @ X23 @ ( k10_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['164','170'])).

thf('172',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['129','130','131','136'])).

thf('173',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('176',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('178',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('179',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('181',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['176','181'])).

thf('183',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['141','148','149','150'])).

thf('184',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['173','184'])).

thf('186',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('187',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['134','135'])).

thf('189',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','189'])).

thf('191',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['152','190'])).

thf('192',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['191','192'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eE2ySn6zUi
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.89  % Solved by: fo/fo7.sh
% 0.69/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.89  % done 674 iterations in 0.435s
% 0.69/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.89  % SZS output start Refutation
% 0.69/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.89  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.69/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.89  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.69/0.89  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.89  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.69/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.89  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.69/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.69/0.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.69/0.89  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.69/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.89  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.69/0.89  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.69/0.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.69/0.89  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.69/0.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.69/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.89  thf(dt_k2_funct_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.89       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.69/0.89         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.69/0.89  thf('0', plain,
% 0.69/0.89      (![X21 : $i]:
% 0.69/0.89         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.69/0.89          | ~ (v1_funct_1 @ X21)
% 0.69/0.89          | ~ (v1_relat_1 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.69/0.89  thf(t61_funct_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.89       ( ( v2_funct_1 @ A ) =>
% 0.69/0.89         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.69/0.89             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.69/0.89           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.69/0.89             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.69/0.89  thf('1', plain,
% 0.69/0.89      (![X25 : $i]:
% 0.69/0.89         (~ (v2_funct_1 @ X25)
% 0.69/0.89          | ((k5_relat_1 @ X25 @ (k2_funct_1 @ X25))
% 0.69/0.89              = (k6_relat_1 @ (k1_relat_1 @ X25)))
% 0.69/0.89          | ~ (v1_funct_1 @ X25)
% 0.69/0.89          | ~ (v1_relat_1 @ X25))),
% 0.69/0.89      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.69/0.89  thf(redefinition_k6_partfun1, axiom,
% 0.69/0.89    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.69/0.89  thf('2', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.89  thf('3', plain,
% 0.69/0.89      (![X25 : $i]:
% 0.69/0.89         (~ (v2_funct_1 @ X25)
% 0.69/0.89          | ((k5_relat_1 @ X25 @ (k2_funct_1 @ X25))
% 0.69/0.89              = (k6_partfun1 @ (k1_relat_1 @ X25)))
% 0.69/0.89          | ~ (v1_funct_1 @ X25)
% 0.69/0.89          | ~ (v1_relat_1 @ X25))),
% 0.69/0.89      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.89  thf('4', plain,
% 0.69/0.89      (![X21 : $i]:
% 0.69/0.89         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.69/0.89          | ~ (v1_funct_1 @ X21)
% 0.69/0.89          | ~ (v1_relat_1 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.69/0.89  thf('5', plain,
% 0.69/0.89      (![X25 : $i]:
% 0.69/0.89         (~ (v2_funct_1 @ X25)
% 0.69/0.89          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 0.69/0.89              = (k6_relat_1 @ (k2_relat_1 @ X25)))
% 0.69/0.89          | ~ (v1_funct_1 @ X25)
% 0.69/0.89          | ~ (v1_relat_1 @ X25))),
% 0.69/0.89      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.69/0.89  thf('6', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.89  thf('7', plain,
% 0.69/0.89      (![X25 : $i]:
% 0.69/0.89         (~ (v2_funct_1 @ X25)
% 0.69/0.89          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 0.69/0.89              = (k6_partfun1 @ (k2_relat_1 @ X25)))
% 0.69/0.89          | ~ (v1_funct_1 @ X25)
% 0.69/0.89          | ~ (v1_relat_1 @ X25))),
% 0.69/0.89      inference('demod', [status(thm)], ['5', '6'])).
% 0.69/0.89  thf('8', plain,
% 0.69/0.89      (![X21 : $i]:
% 0.69/0.89         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.69/0.89          | ~ (v1_funct_1 @ X21)
% 0.69/0.89          | ~ (v1_relat_1 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.69/0.89  thf('9', plain,
% 0.69/0.89      (![X21 : $i]:
% 0.69/0.89         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.69/0.89          | ~ (v1_funct_1 @ X21)
% 0.69/0.89          | ~ (v1_relat_1 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.69/0.89  thf(t55_funct_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.89       ( ( v2_funct_1 @ A ) =>
% 0.69/0.89         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.69/0.89           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.89  thf('10', plain,
% 0.69/0.89      (![X24 : $i]:
% 0.69/0.89         (~ (v2_funct_1 @ X24)
% 0.69/0.89          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 0.69/0.89          | ~ (v1_funct_1 @ X24)
% 0.69/0.89          | ~ (v1_relat_1 @ X24))),
% 0.69/0.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.69/0.89  thf('11', plain,
% 0.69/0.89      (![X21 : $i]:
% 0.69/0.89         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.69/0.89          | ~ (v1_funct_1 @ X21)
% 0.69/0.89          | ~ (v1_relat_1 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.69/0.89  thf(t36_funct_2, conjecture,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.89       ( ![D:$i]:
% 0.69/0.89         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.89             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.89           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.69/0.89               ( r2_relset_1 @
% 0.69/0.89                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.69/0.89                 ( k6_partfun1 @ A ) ) & 
% 0.69/0.89               ( v2_funct_1 @ C ) ) =>
% 0.69/0.89             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.89               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.69/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.89        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.89            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.89          ( ![D:$i]:
% 0.69/0.89            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.89                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.89              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.69/0.89                  ( r2_relset_1 @
% 0.69/0.89                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.69/0.89                    ( k6_partfun1 @ A ) ) & 
% 0.69/0.89                  ( v2_funct_1 @ C ) ) =>
% 0.69/0.89                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.89                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.69/0.89    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.69/0.89  thf('12', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(redefinition_k2_relset_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.89       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.69/0.89  thf('13', plain,
% 0.69/0.89      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.69/0.89         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.69/0.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.69/0.89  thf('14', plain,
% 0.69/0.89      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.69/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.89  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('16', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.89      inference('sup+', [status(thm)], ['14', '15'])).
% 0.69/0.89  thf('17', plain,
% 0.69/0.89      (![X21 : $i]:
% 0.69/0.89         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.69/0.89          | ~ (v1_funct_1 @ X21)
% 0.69/0.89          | ~ (v1_relat_1 @ X21))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.69/0.89  thf('18', plain,
% 0.69/0.89      (![X24 : $i]:
% 0.69/0.89         (~ (v2_funct_1 @ X24)
% 0.69/0.89          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 0.69/0.89          | ~ (v1_funct_1 @ X24)
% 0.69/0.89          | ~ (v1_relat_1 @ X24))),
% 0.69/0.89      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.69/0.89  thf(d10_xboole_0, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.89  thf('19', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.69/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.89  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.69/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.69/0.89  thf(d18_relat_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ B ) =>
% 0.69/0.89       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.69/0.89  thf('21', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.69/0.89          | (v4_relat_1 @ X5 @ X6)
% 0.69/0.89          | ~ (v1_relat_1 @ X5))),
% 0.69/0.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.69/0.89  thf('22', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['20', '21'])).
% 0.69/0.89  thf('23', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | ~ (v2_funct_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['18', '22'])).
% 0.69/0.89  thf('24', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | ~ (v2_funct_1 @ X0)
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['17', '23'])).
% 0.69/0.89  thf('25', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.69/0.89          | ~ (v2_funct_1 @ X0)
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('simplify', [status(thm)], ['24'])).
% 0.69/0.89  thf('26', plain,
% 0.69/0.89      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C)
% 0.69/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89        | ~ (v2_funct_1 @ sk_C))),
% 0.69/0.89      inference('sup+', [status(thm)], ['16', '25'])).
% 0.69/0.89  thf('27', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(cc2_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.69/0.89  thf('28', plain,
% 0.69/0.89      (![X3 : $i, X4 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.69/0.89          | (v1_relat_1 @ X3)
% 0.69/0.89          | ~ (v1_relat_1 @ X4))),
% 0.69/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.89  thf('29', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.69/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.89  thf(fc6_relat_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.89  thf('30', plain,
% 0.69/0.89      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.89  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('34', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 0.69/0.89      inference('demod', [status(thm)], ['26', '31', '32', '33'])).
% 0.69/0.89  thf('35', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (~ (v4_relat_1 @ X5 @ X6)
% 0.69/0.89          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.69/0.89          | ~ (v1_relat_1 @ X5))),
% 0.69/0.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.69/0.89  thf('36', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.69/0.89        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.69/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.69/0.89  thf('37', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ sk_C)
% 0.69/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.69/0.89      inference('sup-', [status(thm)], ['11', '36'])).
% 0.69/0.89  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.69/0.89      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.69/0.89  thf('41', plain,
% 0.69/0.89      (![X0 : $i, X2 : $i]:
% 0.69/0.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.69/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.89  thf('42', plain,
% 0.69/0.89      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.69/0.89        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.69/0.89  thf('43', plain,
% 0.69/0.89      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C)
% 0.69/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89        | ~ (v2_funct_1 @ sk_C)
% 0.69/0.89        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['10', '42'])).
% 0.69/0.89  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.89      inference('sup+', [status(thm)], ['14', '15'])).
% 0.69/0.89  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.69/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.69/0.89  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('49', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.89      inference('demod', [status(thm)], ['43', '44', '45', '46', '47', '48'])).
% 0.69/0.89  thf(t78_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.69/0.89  thf('50', plain,
% 0.69/0.89      (![X19 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 0.69/0.89          | ~ (v1_relat_1 @ X19))),
% 0.69/0.89      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.69/0.89  thf('51', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.89  thf('52', plain,
% 0.69/0.89      (![X19 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 0.69/0.89          | ~ (v1_relat_1 @ X19))),
% 0.69/0.89      inference('demod', [status(thm)], ['50', '51'])).
% 0.69/0.89  thf('53', plain,
% 0.69/0.89      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.69/0.89          = (k2_funct_1 @ sk_C))
% 0.69/0.89        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['49', '52'])).
% 0.69/0.89  thf('54', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ sk_C)
% 0.69/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.69/0.89            = (k2_funct_1 @ sk_C)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['9', '53'])).
% 0.69/0.89  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('57', plain,
% 0.69/0.89      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.69/0.89         = (k2_funct_1 @ sk_C))),
% 0.69/0.89      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.69/0.89  thf(t55_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( v1_relat_1 @ B ) =>
% 0.69/0.89           ( ![C:$i]:
% 0.69/0.89             ( ( v1_relat_1 @ C ) =>
% 0.69/0.89               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.69/0.89                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.69/0.89  thf('58', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X14)
% 0.69/0.89          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 0.69/0.89              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 0.69/0.89          | ~ (v1_relat_1 @ X16)
% 0.69/0.89          | ~ (v1_relat_1 @ X15))),
% 0.69/0.89      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.69/0.89  thf('59', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.69/0.89            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.69/0.89               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.69/0.89          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['57', '58'])).
% 0.69/0.89  thf(t29_relset_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( m1_subset_1 @
% 0.69/0.89       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.69/0.89  thf('60', plain,
% 0.69/0.89      (![X36 : $i]:
% 0.69/0.89         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 0.69/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.69/0.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.69/0.89  thf('61', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.89  thf('62', plain,
% 0.69/0.89      (![X36 : $i]:
% 0.69/0.89         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.69/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.69/0.89      inference('demod', [status(thm)], ['60', '61'])).
% 0.69/0.89  thf('63', plain,
% 0.69/0.89      (![X3 : $i, X4 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.69/0.89          | (v1_relat_1 @ X3)
% 0.69/0.89          | ~ (v1_relat_1 @ X4))),
% 0.69/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.89  thf('64', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.69/0.89          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['62', '63'])).
% 0.69/0.89  thf('65', plain,
% 0.69/0.89      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.89  thf('66', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['64', '65'])).
% 0.69/0.89  thf('67', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.69/0.89            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.69/0.89               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.89      inference('demod', [status(thm)], ['59', '66'])).
% 0.69/0.89  thf('68', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ sk_C)
% 0.69/0.89          | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.69/0.89              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.69/0.89                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['8', '67'])).
% 0.69/0.89  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('71', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.69/0.89              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.69/0.89                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.69/0.89      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.69/0.89  thf('72', plain,
% 0.69/0.89      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.69/0.89          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.69/0.89             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C)
% 0.69/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89        | ~ (v2_funct_1 @ sk_C)
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.89      inference('sup+', [status(thm)], ['7', '71'])).
% 0.69/0.89  thf('73', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.89      inference('sup+', [status(thm)], ['14', '15'])).
% 0.69/0.89  thf(t71_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.69/0.89       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.69/0.89  thf('74', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.69/0.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.69/0.89  thf('75', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.89  thf('76', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.69/0.89      inference('demod', [status(thm)], ['74', '75'])).
% 0.69/0.89  thf('77', plain,
% 0.69/0.89      (![X19 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 0.69/0.89          | ~ (v1_relat_1 @ X19))),
% 0.69/0.89      inference('demod', [status(thm)], ['50', '51'])).
% 0.69/0.89  thf('78', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.69/0.89            = (k6_partfun1 @ X0))
% 0.69/0.89          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['76', '77'])).
% 0.69/0.89  thf('79', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['64', '65'])).
% 0.69/0.89  thf('80', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.69/0.89           = (k6_partfun1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['78', '79'])).
% 0.69/0.89  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('85', plain,
% 0.69/0.89      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.69/0.89      inference('demod', [status(thm)],
% 0.69/0.89                ['72', '73', '80', '81', '82', '83', '84'])).
% 0.69/0.89  thf('86', plain,
% 0.69/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X14)
% 0.69/0.89          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 0.69/0.89              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 0.69/0.89          | ~ (v1_relat_1 @ X16)
% 0.69/0.89          | ~ (v1_relat_1 @ X15))),
% 0.69/0.89      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.69/0.89  thf('87', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.69/0.89            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.69/0.89          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.89      inference('sup+', [status(thm)], ['85', '86'])).
% 0.69/0.89  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('89', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.69/0.89            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.69/0.89          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.69/0.89          | ~ (v1_relat_1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['87', '88'])).
% 0.69/0.89  thf('90', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ sk_C)
% 0.69/0.89          | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89          | ~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.69/0.89              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['4', '89'])).
% 0.69/0.89  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('93', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.69/0.89              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.69/0.89      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.69/0.89  thf('94', plain,
% 0.69/0.89      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.69/0.89          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.69/0.89             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C)
% 0.69/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89        | ~ (v2_funct_1 @ sk_C)
% 0.69/0.89        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.89      inference('sup+', [status(thm)], ['3', '93'])).
% 0.69/0.89  thf('95', plain,
% 0.69/0.89      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.69/0.89         = (k2_funct_1 @ sk_C))),
% 0.69/0.89      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.69/0.89  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('99', plain,
% 0.69/0.89      ((((k2_funct_1 @ sk_C)
% 0.69/0.89          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.69/0.89             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 0.69/0.89        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.89      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.69/0.89  thf('100', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ sk_C)
% 0.69/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89        | ((k2_funct_1 @ sk_C)
% 0.69/0.89            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.69/0.89               (k6_partfun1 @ (k1_relat_1 @ sk_C)))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['0', '99'])).
% 0.69/0.89  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('103', plain,
% 0.69/0.89      (((k2_funct_1 @ sk_C)
% 0.69/0.89         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.69/0.89            (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 0.69/0.89      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.69/0.89  thf('104', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('105', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(redefinition_k1_partfun1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.89     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.89         ( v1_funct_1 @ F ) & 
% 0.69/0.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.89       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.69/0.89  thf('106', plain,
% 0.69/0.89      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.69/0.89          | ~ (v1_funct_1 @ X43)
% 0.69/0.89          | ~ (v1_funct_1 @ X46)
% 0.69/0.89          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.69/0.89          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 0.69/0.89              = (k5_relat_1 @ X43 @ X46)))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.69/0.89  thf('107', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.89            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.89          | ~ (v1_funct_1 @ X0)
% 0.69/0.89          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.89      inference('sup-', [status(thm)], ['105', '106'])).
% 0.69/0.89  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('109', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.89            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.89          | ~ (v1_funct_1 @ X0))),
% 0.69/0.89      inference('demod', [status(thm)], ['107', '108'])).
% 0.69/0.89  thf('110', plain,
% 0.69/0.89      ((~ (v1_funct_1 @ sk_D)
% 0.69/0.89        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.89            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['104', '109'])).
% 0.69/0.89  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('112', plain,
% 0.69/0.89      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.89        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.89        (k6_partfun1 @ sk_A))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('113', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('114', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(dt_k1_partfun1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.89     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.89         ( v1_funct_1 @ F ) & 
% 0.69/0.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.89       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.69/0.89         ( m1_subset_1 @
% 0.69/0.89           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.69/0.89           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.69/0.89  thf('115', plain,
% 0.69/0.89      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.69/0.89          | ~ (v1_funct_1 @ X37)
% 0.69/0.89          | ~ (v1_funct_1 @ X40)
% 0.69/0.89          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.69/0.89          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 0.69/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 0.69/0.89      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.69/0.89  thf('116', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.69/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.69/0.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.69/0.89          | ~ (v1_funct_1 @ X1)
% 0.69/0.89          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.89      inference('sup-', [status(thm)], ['114', '115'])).
% 0.69/0.89  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('118', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.89         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.69/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.69/0.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.69/0.89          | ~ (v1_funct_1 @ X1))),
% 0.69/0.89      inference('demod', [status(thm)], ['116', '117'])).
% 0.69/0.89  thf('119', plain,
% 0.69/0.89      ((~ (v1_funct_1 @ sk_D)
% 0.69/0.89        | (m1_subset_1 @ 
% 0.69/0.89           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['113', '118'])).
% 0.69/0.89  thf('120', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('121', plain,
% 0.69/0.89      ((m1_subset_1 @ 
% 0.69/0.89        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['119', '120'])).
% 0.69/0.89  thf(redefinition_r2_relset_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.89     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.89       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.69/0.89  thf('122', plain,
% 0.69/0.89      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.69/0.89          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.69/0.89          | ((X32) = (X35))
% 0.69/0.89          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 0.69/0.89      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.69/0.89  thf('123', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.89             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.69/0.89          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.69/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.69/0.89      inference('sup-', [status(thm)], ['121', '122'])).
% 0.69/0.89  thf('124', plain,
% 0.69/0.89      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.69/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.69/0.89        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.89            = (k6_partfun1 @ sk_A)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['112', '123'])).
% 0.69/0.89  thf('125', plain,
% 0.69/0.89      (![X36 : $i]:
% 0.69/0.89         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.69/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.69/0.89      inference('demod', [status(thm)], ['60', '61'])).
% 0.69/0.89  thf('126', plain,
% 0.69/0.89      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.89         = (k6_partfun1 @ sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['124', '125'])).
% 0.69/0.89  thf('127', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.69/0.89      inference('demod', [status(thm)], ['110', '111', '126'])).
% 0.69/0.89  thf(t182_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ![B:$i]:
% 0.69/0.89         ( ( v1_relat_1 @ B ) =>
% 0.69/0.89           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.69/0.89             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.69/0.89  thf('128', plain,
% 0.69/0.89      (![X12 : $i, X13 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X12)
% 0.69/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.69/0.89              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.69/0.89          | ~ (v1_relat_1 @ X13))),
% 0.69/0.89      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.69/0.89  thf('129', plain,
% 0.69/0.89      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.69/0.89          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C)
% 0.69/0.89        | ~ (v1_relat_1 @ sk_D))),
% 0.69/0.89      inference('sup+', [status(thm)], ['127', '128'])).
% 0.69/0.89  thf('130', plain,
% 0.69/0.89      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.69/0.89      inference('demod', [status(thm)], ['74', '75'])).
% 0.69/0.89  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('132', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('133', plain,
% 0.69/0.89      (![X3 : $i, X4 : $i]:
% 0.69/0.89         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.69/0.89          | (v1_relat_1 @ X3)
% 0.69/0.89          | ~ (v1_relat_1 @ X4))),
% 0.69/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.89  thf('134', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.69/0.89      inference('sup-', [status(thm)], ['132', '133'])).
% 0.69/0.89  thf('135', plain,
% 0.69/0.89      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.69/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.89  thf('136', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['134', '135'])).
% 0.69/0.89  thf('137', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.69/0.89      inference('demod', [status(thm)], ['129', '130', '131', '136'])).
% 0.69/0.89  thf(t167_relat_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ B ) =>
% 0.69/0.89       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.69/0.89  thf('138', plain,
% 0.69/0.89      (![X9 : $i, X10 : $i]:
% 0.69/0.89         ((r1_tarski @ (k10_relat_1 @ X9 @ X10) @ (k1_relat_1 @ X9))
% 0.69/0.89          | ~ (v1_relat_1 @ X9))),
% 0.69/0.89      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.69/0.89  thf('139', plain,
% 0.69/0.89      (![X0 : $i, X2 : $i]:
% 0.69/0.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.69/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.89  thf('140', plain,
% 0.69/0.89      (![X0 : $i, X1 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.69/0.89          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['138', '139'])).
% 0.69/0.89  thf('141', plain,
% 0.69/0.89      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)
% 0.69/0.89        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.89      inference('sup-', [status(thm)], ['137', '140'])).
% 0.69/0.89  thf('142', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf(cc2_relset_1, axiom,
% 0.69/0.89    (![A:$i,B:$i,C:$i]:
% 0.69/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.69/0.89  thf('143', plain,
% 0.69/0.89      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.89         ((v4_relat_1 @ X26 @ X27)
% 0.69/0.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.69/0.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.69/0.89  thf('144', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.69/0.89      inference('sup-', [status(thm)], ['142', '143'])).
% 0.69/0.89  thf('145', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (~ (v4_relat_1 @ X5 @ X6)
% 0.69/0.89          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.69/0.89          | ~ (v1_relat_1 @ X5))),
% 0.69/0.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.69/0.89  thf('146', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.69/0.89      inference('sup-', [status(thm)], ['144', '145'])).
% 0.69/0.89  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('148', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.69/0.89      inference('demod', [status(thm)], ['146', '147'])).
% 0.69/0.89  thf('149', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.69/0.89      inference('demod', [status(thm)], ['129', '130', '131', '136'])).
% 0.69/0.89  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('151', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['141', '148', '149', '150'])).
% 0.69/0.89  thf('152', plain,
% 0.69/0.89      (((k2_funct_1 @ sk_C)
% 0.69/0.89         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['103', '151'])).
% 0.69/0.89  thf('153', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.69/0.89      inference('demod', [status(thm)], ['110', '111', '126'])).
% 0.69/0.89  thf('154', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (v1_relat_1 @ X0)
% 0.69/0.89          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.69/0.89              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.69/0.89      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.69/0.89  thf('155', plain,
% 0.69/0.89      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 0.69/0.89          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_D))),
% 0.69/0.89      inference('sup+', [status(thm)], ['153', '154'])).
% 0.69/0.89  thf('156', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['134', '135'])).
% 0.69/0.89  thf('157', plain,
% 0.69/0.89      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 0.69/0.89         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['155', '156'])).
% 0.69/0.89  thf('158', plain,
% 0.69/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('159', plain,
% 0.69/0.89      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.89         ((v4_relat_1 @ X26 @ X27)
% 0.69/0.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.69/0.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.69/0.89  thf('160', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.69/0.89      inference('sup-', [status(thm)], ['158', '159'])).
% 0.69/0.89  thf('161', plain,
% 0.69/0.89      (![X5 : $i, X6 : $i]:
% 0.69/0.89         (~ (v4_relat_1 @ X5 @ X6)
% 0.69/0.89          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.69/0.89          | ~ (v1_relat_1 @ X5))),
% 0.69/0.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.69/0.89  thf('162', plain,
% 0.69/0.89      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.69/0.89      inference('sup-', [status(thm)], ['160', '161'])).
% 0.69/0.89  thf('163', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['134', '135'])).
% 0.69/0.89  thf('164', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.69/0.89      inference('demod', [status(thm)], ['162', '163'])).
% 0.69/0.89  thf('165', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.89      inference('sup+', [status(thm)], ['14', '15'])).
% 0.69/0.89  thf(t147_funct_1, axiom,
% 0.69/0.89    (![A:$i,B:$i]:
% 0.69/0.89     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.89       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.69/0.89         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.69/0.89  thf('166', plain,
% 0.69/0.89      (![X22 : $i, X23 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X22 @ (k2_relat_1 @ X23))
% 0.69/0.89          | ((k9_relat_1 @ X23 @ (k10_relat_1 @ X23 @ X22)) = (X22))
% 0.69/0.89          | ~ (v1_funct_1 @ X23)
% 0.69/0.89          | ~ (v1_relat_1 @ X23))),
% 0.69/0.89      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.69/0.89  thf('167', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X0 @ sk_B)
% 0.69/0.89          | ~ (v1_relat_1 @ sk_C)
% 0.69/0.89          | ~ (v1_funct_1 @ sk_C)
% 0.69/0.89          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.69/0.89      inference('sup-', [status(thm)], ['165', '166'])).
% 0.69/0.89  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('170', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X0 @ sk_B)
% 0.69/0.89          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['167', '168', '169'])).
% 0.69/0.89  thf('171', plain,
% 0.69/0.89      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.69/0.89         = (k1_relat_1 @ sk_D))),
% 0.69/0.89      inference('sup-', [status(thm)], ['164', '170'])).
% 0.69/0.89  thf('172', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.69/0.89      inference('demod', [status(thm)], ['129', '130', '131', '136'])).
% 0.69/0.89  thf('173', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.69/0.89      inference('demod', [status(thm)], ['171', '172'])).
% 0.69/0.89  thf('174', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.69/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.69/0.89  thf('175', plain,
% 0.69/0.89      (![X0 : $i]:
% 0.69/0.89         (~ (r1_tarski @ X0 @ sk_B)
% 0.69/0.89          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.69/0.89      inference('demod', [status(thm)], ['167', '168', '169'])).
% 0.69/0.89  thf('176', plain,
% 0.69/0.89      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.69/0.89      inference('sup-', [status(thm)], ['174', '175'])).
% 0.69/0.89  thf('177', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.89      inference('sup+', [status(thm)], ['14', '15'])).
% 0.69/0.89  thf(t169_relat_1, axiom,
% 0.69/0.89    (![A:$i]:
% 0.69/0.89     ( ( v1_relat_1 @ A ) =>
% 0.69/0.89       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.69/0.89  thf('178', plain,
% 0.69/0.89      (![X11 : $i]:
% 0.69/0.89         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 0.69/0.89          | ~ (v1_relat_1 @ X11))),
% 0.69/0.89      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.69/0.89  thf('179', plain,
% 0.69/0.89      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.89      inference('sup+', [status(thm)], ['177', '178'])).
% 0.69/0.89  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.89  thf('181', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.69/0.89      inference('demod', [status(thm)], ['179', '180'])).
% 0.69/0.89  thf('182', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_B))),
% 0.69/0.89      inference('demod', [status(thm)], ['176', '181'])).
% 0.69/0.89  thf('183', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.69/0.89      inference('demod', [status(thm)], ['141', '148', '149', '150'])).
% 0.69/0.89  thf('184', plain, (((k9_relat_1 @ sk_C @ sk_A) = (sk_B))),
% 0.69/0.89      inference('demod', [status(thm)], ['182', '183'])).
% 0.69/0.89  thf('185', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.69/0.89      inference('sup+', [status(thm)], ['173', '184'])).
% 0.69/0.89  thf('186', plain,
% 0.69/0.89      (![X19 : $i]:
% 0.69/0.89         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 0.69/0.89          | ~ (v1_relat_1 @ X19))),
% 0.69/0.89      inference('demod', [status(thm)], ['50', '51'])).
% 0.69/0.89  thf('187', plain,
% 0.69/0.89      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 0.69/0.89        | ~ (v1_relat_1 @ sk_D))),
% 0.69/0.89      inference('sup+', [status(thm)], ['185', '186'])).
% 0.69/0.89  thf('188', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.89      inference('demod', [status(thm)], ['134', '135'])).
% 0.69/0.89  thf('189', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.69/0.89      inference('demod', [status(thm)], ['187', '188'])).
% 0.69/0.89  thf('190', plain,
% 0.69/0.89      (((sk_D) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 0.69/0.89      inference('demod', [status(thm)], ['157', '189'])).
% 0.69/0.89  thf('191', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.69/0.89      inference('sup+', [status(thm)], ['152', '190'])).
% 0.69/0.89  thf('192', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.69/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.89  thf('193', plain, ($false),
% 0.69/0.89      inference('simplify_reflect-', [status(thm)], ['191', '192'])).
% 0.69/0.89  
% 0.69/0.89  % SZS output end Refutation
% 0.69/0.89  
% 0.69/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
