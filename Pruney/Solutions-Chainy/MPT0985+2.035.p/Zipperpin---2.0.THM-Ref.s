%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LsY14x3iSS

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:31 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  149 (2003 expanded)
%              Number of leaves         :   35 ( 605 expanded)
%              Depth                    :   32
%              Number of atoms          : 1183 (33108 expanded)
%              Number of equality atoms :   43 ( 918 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('17',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['10','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

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

thf('35',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( zip_tseitin_1 @ X26 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( zip_tseitin_0 @ X29 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf('39',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('41',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('42',plain,(
    ! [X20: $i] :
      ( ( v1_funct_2 @ X20 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['38','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','62'])).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('65',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('69',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('71',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','62'])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf('79',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('81',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('85',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('86',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf('89',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('93',plain,(
    ! [X24: $i] :
      ~ ( zip_tseitin_1 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('96',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['74','94','95'])).

thf('97',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['67','96'])).

thf('98',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['65','97'])).

thf('99',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['65','97'])).

thf('100',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('104',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('105',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf('108',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['102','109'])).

thf('111',plain,(
    ! [X24: $i] :
      ~ ( zip_tseitin_1 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('112',plain,(
    $false ),
    inference('sup-',[status(thm)],['110','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LsY14x3iSS
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 324 iterations in 0.145s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.41/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(t31_funct_2, conjecture,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.41/0.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.41/0.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.41/0.62           ( m1_subset_1 @
% 0.41/0.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.41/0.62            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.41/0.62              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.41/0.62              ( m1_subset_1 @
% 0.41/0.62                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc2_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.62         ((v4_relat_1 @ X8 @ X9)
% 0.41/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.62  thf('2', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.62  thf(d18_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ B ) =>
% 0.41/0.62       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v4_relat_1 @ X0 @ X1)
% 0.41/0.62          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc1_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( v1_relat_1 @ C ) ))).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((v1_relat_1 @ X5)
% 0.41/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.62  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('8', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['4', '7'])).
% 0.41/0.62  thf(dt_k2_funct_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.41/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X3 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.41/0.62          | ~ (v1_funct_1 @ X3)
% 0.41/0.62          | ~ (v1_relat_1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.62  thf(t55_funct_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.62       ( ( v2_funct_1 @ A ) =>
% 0.41/0.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.41/0.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X4 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X4)
% 0.41/0.62          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.41/0.62          | ~ (v1_funct_1 @ X4)
% 0.41/0.62          | ~ (v1_relat_1 @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.41/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.62  thf('14', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('15', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X3 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.41/0.62          | ~ (v1_funct_1 @ X3)
% 0.41/0.62          | ~ (v1_relat_1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X3 : $i]:
% 0.41/0.62         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.41/0.62          | ~ (v1_funct_1 @ X3)
% 0.41/0.62          | ~ (v1_relat_1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X4 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X4)
% 0.41/0.62          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.41/0.62          | ~ (v1_funct_1 @ X4)
% 0.41/0.62          | ~ (v1_relat_1 @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.62  thf(t3_funct_2, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.62       ( ( v1_funct_1 @ A ) & 
% 0.41/0.62         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.41/0.62         ( m1_subset_1 @
% 0.41/0.62           A @ 
% 0.41/0.62           ( k1_zfmisc_1 @
% 0.41/0.62             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X20 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X20 @ 
% 0.41/0.62           (k1_zfmisc_1 @ 
% 0.41/0.62            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))))
% 0.41/0.62          | ~ (v1_funct_1 @ X20)
% 0.41/0.62          | ~ (v1_relat_1 @ X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.41/0.62           (k1_zfmisc_1 @ 
% 0.41/0.62            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.41/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.41/0.62             (k1_zfmisc_1 @ 
% 0.41/0.62              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.41/0.62               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '20'])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.41/0.62           (k1_zfmisc_1 @ 
% 0.41/0.62            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.41/0.62             (k1_zfmisc_1 @ 
% 0.41/0.62              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.41/0.62               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['16', '22'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.41/0.62           (k1_zfmisc_1 @ 
% 0.41/0.62            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['23'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62         (k1_zfmisc_1 @ 
% 0.41/0.62          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.62      inference('sup+', [status(thm)], ['15', '24'])).
% 0.41/0.62  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('28', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.41/0.62      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.62      inference('sup+', [status(thm)], ['10', '29'])).
% 0.41/0.62  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 0.41/0.62      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.41/0.62  thf(t9_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.62         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.41/0.62       ( ( r1_tarski @ B @ C ) =>
% 0.41/0.62         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.41/0.62             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.41/0.62           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.41/0.62  thf(zf_stmt_2, axiom,
% 0.41/0.62    (![B:$i,A:$i]:
% 0.41/0.62     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.41/0.62       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.41/0.62  thf(zf_stmt_4, axiom,
% 0.41/0.62    (![D:$i,C:$i,A:$i]:
% 0.41/0.62     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.41/0.62       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.41/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_5, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ( r1_tarski @ B @ C ) =>
% 0.41/0.62         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X26 @ X27)
% 0.41/0.62          | (zip_tseitin_1 @ X26 @ X28)
% 0.41/0.62          | ~ (v1_funct_1 @ X29)
% 0.41/0.62          | ~ (v1_funct_2 @ X29 @ X28 @ X26)
% 0.41/0.62          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.41/0.62          | (zip_tseitin_0 @ X29 @ X27 @ X28))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ X0 @ sk_B)
% 0.41/0.62          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 0.41/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.41/0.62          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.41/0.62          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X4 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X4)
% 0.41/0.62          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.41/0.62          | ~ (v1_funct_1 @ X4)
% 0.41/0.62          | ~ (v1_relat_1 @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.62  thf('38', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (![X3 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.41/0.62          | ~ (v1_funct_1 @ X3)
% 0.41/0.62          | ~ (v1_relat_1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      (![X3 : $i]:
% 0.41/0.62         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 0.41/0.62          | ~ (v1_funct_1 @ X3)
% 0.41/0.62          | ~ (v1_relat_1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      (![X4 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X4)
% 0.41/0.62          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.41/0.62          | ~ (v1_funct_1 @ X4)
% 0.41/0.62          | ~ (v1_relat_1 @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X20 : $i]:
% 0.41/0.62         ((v1_funct_2 @ X20 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))
% 0.41/0.62          | ~ (v1_funct_1 @ X20)
% 0.41/0.62          | ~ (v1_relat_1 @ X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.41/0.62           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.41/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['41', '42'])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.41/0.62             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['40', '43'])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.41/0.62           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['44'])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.41/0.62             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['39', '45'])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.41/0.62           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.41/0.62          | ~ (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 0.41/0.62         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.62      inference('sup+', [status(thm)], ['38', '47'])).
% 0.41/0.62  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 0.41/0.62        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.62      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.62      inference('sup+', [status(thm)], ['37', '52'])).
% 0.41/0.62  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.41/0.62      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ X0 @ sk_B)
% 0.41/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.41/0.62          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.41/0.62          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['36', '57'])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ sk_C)
% 0.41/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.41/0.62          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.41/0.62          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ X0 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['9', '58'])).
% 0.41/0.62  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('62', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.41/0.62          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.41/0.62          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ X0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.41/0.62  thf('63', plain,
% 0.41/0.62      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.41/0.62        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['8', '62'])).
% 0.41/0.62  thf('64', plain,
% 0.41/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.41/0.62          | ~ (zip_tseitin_0 @ X21 @ X22 @ X23))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.62  thf('65', plain,
% 0.41/0.62      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.41/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.41/0.62  thf('66', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.41/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.41/0.62        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('67', plain,
% 0.41/0.62      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.41/0.62         <= (~
% 0.41/0.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.41/0.62      inference('split', [status(esa)], ['66'])).
% 0.41/0.62  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('69', plain,
% 0.41/0.62      (![X3 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 0.41/0.62          | ~ (v1_funct_1 @ X3)
% 0.41/0.62          | ~ (v1_relat_1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.41/0.62  thf('70', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.41/0.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.41/0.62      inference('split', [status(esa)], ['66'])).
% 0.41/0.62  thf('71', plain,
% 0.41/0.62      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.41/0.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.62  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.41/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.41/0.62  thf('74', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['68', '73'])).
% 0.41/0.62  thf('75', plain,
% 0.41/0.62      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.41/0.62        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['8', '62'])).
% 0.41/0.62  thf('76', plain,
% 0.41/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.62         ((v1_funct_2 @ X21 @ X23 @ X22) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.62  thf('77', plain,
% 0.41/0.62      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)
% 0.41/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.41/0.62  thf('78', plain,
% 0.41/0.62      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('split', [status(esa)], ['66'])).
% 0.41/0.62  thf('79', plain,
% 0.41/0.62      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.41/0.62  thf('80', plain,
% 0.41/0.62      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.41/0.62  thf('81', plain,
% 0.41/0.62      (![X24 : $i, X25 : $i]:
% 0.41/0.62         (((X24) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X24 @ X25))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.62  thf('82', plain,
% 0.41/0.62      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.62  thf('83', plain,
% 0.41/0.62      (((zip_tseitin_1 @ k1_xboole_0 @ sk_B))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['79', '82'])).
% 0.41/0.62  thf('84', plain,
% 0.41/0.62      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.62  thf(t65_relat_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ A ) =>
% 0.41/0.62       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.62         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.62  thf('85', plain,
% 0.41/0.62      (![X2 : $i]:
% 0.41/0.62         (((k1_relat_1 @ X2) != (k1_xboole_0))
% 0.41/0.62          | ((k2_relat_1 @ X2) = (k1_xboole_0))
% 0.41/0.62          | ~ (v1_relat_1 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.41/0.62  thf('86', plain,
% 0.41/0.62      (((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.62         | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62         | ((k2_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.41/0.62  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('88', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.62  thf('89', plain,
% 0.41/0.62      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.41/0.62  thf('90', plain,
% 0.41/0.62      ((((sk_B) = (k1_xboole_0)))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['89'])).
% 0.41/0.62  thf('91', plain,
% 0.41/0.62      (((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.41/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['83', '90'])).
% 0.41/0.62  thf('92', plain,
% 0.41/0.62      (![X24 : $i, X25 : $i]:
% 0.41/0.62         (((X25) != (k1_xboole_0)) | ~ (zip_tseitin_1 @ X24 @ X25))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.62  thf('93', plain, (![X24 : $i]: ~ (zip_tseitin_1 @ X24 @ k1_xboole_0)),
% 0.41/0.62      inference('simplify', [status(thm)], ['92'])).
% 0.41/0.62  thf('94', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['91', '93'])).
% 0.41/0.62  thf('95', plain,
% 0.41/0.62      (~
% 0.41/0.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.41/0.62       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.41/0.62       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.62      inference('split', [status(esa)], ['66'])).
% 0.41/0.62  thf('96', plain,
% 0.41/0.62      (~
% 0.41/0.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['74', '94', '95'])).
% 0.41/0.62  thf('97', plain,
% 0.41/0.62      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('simpl_trail', [status(thm)], ['67', '96'])).
% 0.41/0.62  thf('98', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.41/0.62      inference('clc', [status(thm)], ['65', '97'])).
% 0.41/0.62  thf('99', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.41/0.62      inference('clc', [status(thm)], ['65', '97'])).
% 0.41/0.62  thf('100', plain,
% 0.41/0.62      (![X24 : $i, X25 : $i]:
% 0.41/0.62         (((X24) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X24 @ X25))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.62  thf('101', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.41/0.62  thf('102', plain, ((zip_tseitin_1 @ k1_xboole_0 @ sk_B)),
% 0.41/0.62      inference('demod', [status(thm)], ['98', '101'])).
% 0.41/0.62  thf('103', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.41/0.62  thf('104', plain,
% 0.41/0.62      (![X2 : $i]:
% 0.41/0.62         (((k1_relat_1 @ X2) != (k1_xboole_0))
% 0.41/0.62          | ((k2_relat_1 @ X2) = (k1_xboole_0))
% 0.41/0.62          | ~ (v1_relat_1 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.41/0.62  thf('105', plain,
% 0.41/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['103', '104'])).
% 0.41/0.62  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('107', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.62  thf('108', plain,
% 0.41/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.41/0.62  thf('109', plain, (((sk_B) = (k1_xboole_0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['108'])).
% 0.41/0.62  thf('110', plain, ((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('demod', [status(thm)], ['102', '109'])).
% 0.41/0.62  thf('111', plain, (![X24 : $i]: ~ (zip_tseitin_1 @ X24 @ k1_xboole_0)),
% 0.41/0.62      inference('simplify', [status(thm)], ['92'])).
% 0.41/0.62  thf('112', plain, ($false), inference('sup-', [status(thm)], ['110', '111'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
