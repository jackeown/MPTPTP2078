%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eEKCdaoYpp

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:12 EST 2020

% Result     : Theorem 3.71s
% Output     : Refutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  424 (212011 expanded)
%              Number of leaves         :   47 (62259 expanded)
%              Depth                    :   25
%              Number of atoms          : 5643 (5159104 expanded)
%              Number of equality atoms :  214 (61628 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('11',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_B )
      = ( k5_relat_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_B )
    = ( k5_relat_1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ( k11_relat_1 @ B @ D )
                  = ( k11_relat_1 @ C @ D ) ) )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ( r2_relset_1 @ X24 @ X24 @ X25 @ X23 )
      | ( r2_hidden @ ( sk_D @ X23 @ X25 @ X24 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_B ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k5_relat_1 @ sk_B @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_B ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('32',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('40',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_2 @ X30 @ X29 )
      | ( ( k2_relat_1 @ X30 )
        = X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['37','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('56',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','53','59','60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('72',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_funct_2 @ X46 @ X45 )
        = ( k2_funct_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) )
      | ~ ( v3_funct_2 @ X45 @ X46 @ X46 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X46 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('89',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','89'])).

thf('91',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('92',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','97'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('99',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('100',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('101',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','77'])).

thf('106',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('114',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['92'])).

thf('115',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('116',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X49 ) @ X49 )
        = ( k6_partfun1 @ X48 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('121',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('122',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X49 ) @ X49 )
        = ( k6_relat_1 @ X48 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['37','52'])).

thf('125',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('126',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('131',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('133',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('135',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('136',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','133','134','135'])).

thf('137',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('138',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( sk_B
      = ( k2_funct_2 @ sk_A @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('144',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('145',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      | ( sk_B
        = ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('147',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('148',plain,
    ( ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      | ( sk_B
        = ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('150',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','77'])).

thf('152',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ( r2_relset_1 @ X24 @ X24 @ X25 @ X23 )
      | ( r2_hidden @ ( sk_D @ X23 @ X25 @ X24 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k2_funct_1 @ sk_B ) @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('156',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','156'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('158',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('159',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('160',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('161',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','161'])).

thf('163',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ sk_B @ sk_B ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','162'])).

thf('164',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('167',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = sk_B )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('171',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('172',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('173',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('174',plain,
    ( ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k6_relat_1 @ k1_xboole_0 )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('175',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('176',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('178',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('180',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('183',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('184',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('185',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('186',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','186'])).

thf('188',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','186'])).

thf('189',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ k1_xboole_0 ) ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','187','188'])).

thf('190',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('191',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','77'])).

thf('193',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ ( k2_funct_1 @ sk_B ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ ( k2_funct_1 @ sk_B ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['191','196'])).

thf('198',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('201',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('203',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) )
      | ( r2_relset_1 @ X24 @ X24 @ X25 @ X23 )
      | ( r2_hidden @ ( sk_D @ X23 @ X25 @ X24 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X1 @ X0 ) @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['201','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('207',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','207'])).

thf('209',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('210',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('211',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('212',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','186'])).

thf('213',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','161'])).

thf('214',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','186'])).

thf('215',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','186'])).

thf('216',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = ( k2_funct_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','186'])).

thf('218',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('219',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('220',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('221',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ X0 @ X0 ) @ X1 @ X0 ) @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ X0 @ X0 ) @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['225','228'])).

thf('230',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('232',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('234',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,
    ( ~ ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['229','234'])).

thf('236',plain,
    ( ( ~ ( r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
        = sk_B )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['220','235'])).

thf('237',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('238',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('239',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('240',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('241',plain,
    ( ( ~ ( r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['236','237','238','239','240'])).

thf('242',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','186'])).

thf('243',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('244',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','186'])).

thf('245',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['241','242','243','244'])).

thf('246',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ k1_xboole_0 ) ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['208','209','210','211','212','216','217','218','219','245'])).

thf('247',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['189','246'])).

thf('248',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['92'])).

thf('249',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['247','248'])).

thf('250',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['103','249'])).

thf('251',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['103','249'])).

thf('252',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['103','249'])).

thf('253',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('254',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ sk_B @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['29','250','251','252','253'])).

thf('255',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('256',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = sk_B )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('257',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('259',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('260',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('261',plain,
    ( ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k6_relat_1 @ k1_xboole_0 )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['257','258','259','260'])).

thf('262',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('263',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('264',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('266',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('267',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('268',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','102'])).

thf('269',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['264','265','266','267','268'])).

thf('270',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['261','269'])).

thf('271',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['247','248'])).

thf('272',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['270','271'])).

thf('274',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['270','271'])).

thf('275',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ k1_xboole_0 ) ) @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['254','272','273','274'])).

thf('276',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','89'])).

thf('277',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('278',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('280',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('281',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['278','279','280'])).

thf('282',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['281'])).

thf('283',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['277','282'])).

thf('284',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['276','283'])).

thf('285',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('286',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['276','283'])).

thf('287',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('289',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('290',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('291',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('292',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['284','289','290','291'])).

thf('293',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('294',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('295',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      | ( sk_B
        = ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('297',plain,
    ( ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      | ( sk_B
        = ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['295','296'])).

thf('298',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('299',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('300',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('302',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('303',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('304',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['300','301','302','303'])).

thf('305',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['297','304'])).

thf('306',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ sk_B @ sk_B ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['292','305'])).

thf('307',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('308',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = sk_B )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('309',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('311',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('312',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('313',plain,
    ( ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k6_relat_1 @ k1_xboole_0 )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['309','310','311','312'])).

thf('314',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('315',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('316',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('318',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('319',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('320',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('321',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['316','317','318','319','320'])).

thf('322',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['313','321'])).

thf('323',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['313','321'])).

thf('324',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ k1_xboole_0 ) ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['306','322','323'])).

thf('325',plain,
    ( $false
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['275','324'])).

thf('326',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ k1_xboole_0 ) ) @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['254','272','273','274'])).

thf('327',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('328',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('329',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['281'])).

thf('330',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['328','329'])).

thf('331',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['327','330'])).

thf('332',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('333',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['327','330'])).

thf('334',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['332','333'])).

thf('335',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('336',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('337',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('338',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('339',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['331','336','337','338'])).

thf('340',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('341',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('342',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      | ( sk_B
        = ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('344',plain,
    ( ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      | ( sk_B
        = ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['342','343'])).

thf('345',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('346',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('347',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('349',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('350',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('351',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ ( k2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['347','348','349','350'])).

thf('352',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['344','351'])).

thf('353',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ sk_B @ sk_B ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['339','352'])).

thf('354',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('355',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = sk_B )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('356',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k6_relat_1 @ sk_A )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['354','355'])).

thf('357',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('358',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('359',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('360',plain,
    ( ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
      | ( ( k6_relat_1 @ k1_xboole_0 )
        = sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['356','357','358','359'])).

thf('361',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('362',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('363',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['361','362'])).

thf('364',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('365',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('366',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('367',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('368',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['363','364','365','366','367'])).

thf('369',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['360','368'])).

thf('370',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['360','368'])).

thf('371',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ k1_xboole_0 ) ) @ ( k6_relat_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['353','369','370'])).

thf('372',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['326','371'])).

thf('373',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['281'])).

thf('374',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['372','373'])).

thf('375',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['325','374'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eEKCdaoYpp
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.71/3.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.71/3.89  % Solved by: fo/fo7.sh
% 3.71/3.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.71/3.89  % done 7888 iterations in 3.381s
% 3.71/3.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.71/3.89  % SZS output start Refutation
% 3.71/3.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.71/3.89  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 3.71/3.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.71/3.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.71/3.89  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.71/3.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.71/3.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.71/3.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.71/3.89  thf(sk_B_type, type, sk_B: $i).
% 3.71/3.89  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.71/3.89  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.71/3.89  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.71/3.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.71/3.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.71/3.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.71/3.89  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 3.71/3.89  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.71/3.89  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 3.71/3.89  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.71/3.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.71/3.89  thf(sk_A_type, type, sk_A: $i).
% 3.71/3.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.71/3.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.71/3.89  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.71/3.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.71/3.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.71/3.89  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.71/3.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.71/3.89  thf(t88_funct_2, conjecture,
% 3.71/3.89    (![A:$i,B:$i]:
% 3.71/3.89     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.71/3.89         ( v3_funct_2 @ B @ A @ A ) & 
% 3.71/3.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.71/3.89       ( ( r2_relset_1 @
% 3.71/3.89           A @ A @ 
% 3.71/3.89           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 3.71/3.89           ( k6_partfun1 @ A ) ) & 
% 3.71/3.89         ( r2_relset_1 @
% 3.71/3.89           A @ A @ 
% 3.71/3.89           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 3.71/3.89           ( k6_partfun1 @ A ) ) ) ))).
% 3.71/3.89  thf(zf_stmt_0, negated_conjecture,
% 3.71/3.89    (~( ![A:$i,B:$i]:
% 3.71/3.89        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.71/3.89            ( v3_funct_2 @ B @ A @ A ) & 
% 3.71/3.89            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.71/3.89          ( ( r2_relset_1 @
% 3.71/3.89              A @ A @ 
% 3.71/3.89              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 3.71/3.89              ( k6_partfun1 @ A ) ) & 
% 3.71/3.89            ( r2_relset_1 @
% 3.71/3.89              A @ A @ 
% 3.71/3.89              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 3.71/3.89              ( k6_partfun1 @ A ) ) ) ) )),
% 3.71/3.89    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 3.71/3.89  thf('0', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('1', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(dt_k1_partfun1, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.71/3.89     ( ( ( v1_funct_1 @ E ) & 
% 3.71/3.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.71/3.89         ( v1_funct_1 @ F ) & 
% 3.71/3.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.71/3.89       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.71/3.89         ( m1_subset_1 @
% 3.71/3.89           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.71/3.89           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.71/3.89  thf('2', plain,
% 3.71/3.89      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.71/3.89          | ~ (v1_funct_1 @ X31)
% 3.71/3.89          | ~ (v1_funct_1 @ X34)
% 3.71/3.89          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.71/3.89          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 3.71/3.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 3.71/3.89      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.71/3.89  thf('3', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 3.71/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.71/3.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.71/3.89          | ~ (v1_funct_1 @ X1)
% 3.71/3.89          | ~ (v1_funct_1 @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['1', '2'])).
% 3.71/3.89  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('5', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 3.71/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.71/3.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.71/3.89          | ~ (v1_funct_1 @ X1))),
% 3.71/3.89      inference('demod', [status(thm)], ['3', '4'])).
% 3.71/3.89  thf('6', plain,
% 3.71/3.89      ((~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | (m1_subset_1 @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_B) @ 
% 3.71/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['0', '5'])).
% 3.71/3.89  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('8', plain,
% 3.71/3.89      ((m1_subset_1 @ 
% 3.71/3.89        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['6', '7'])).
% 3.71/3.89  thf('9', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('10', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(redefinition_k1_partfun1, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.71/3.89     ( ( ( v1_funct_1 @ E ) & 
% 3.71/3.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.71/3.89         ( v1_funct_1 @ F ) & 
% 3.71/3.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.71/3.89       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.71/3.89  thf('11', plain,
% 3.71/3.89      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.71/3.89          | ~ (v1_funct_1 @ X39)
% 3.71/3.89          | ~ (v1_funct_1 @ X42)
% 3.71/3.89          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.71/3.89          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 3.71/3.89              = (k5_relat_1 @ X39 @ X42)))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.71/3.89  thf('12', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 3.71/3.89            = (k5_relat_1 @ sk_B @ X0))
% 3.71/3.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.71/3.89          | ~ (v1_funct_1 @ X0)
% 3.71/3.89          | ~ (v1_funct_1 @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['10', '11'])).
% 3.71/3.89  thf('13', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('14', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 3.71/3.89            = (k5_relat_1 @ sk_B @ X0))
% 3.71/3.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.71/3.89          | ~ (v1_funct_1 @ X0))),
% 3.71/3.89      inference('demod', [status(thm)], ['12', '13'])).
% 3.71/3.89  thf('15', plain,
% 3.71/3.89      ((~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_B)
% 3.71/3.89            = (k5_relat_1 @ sk_B @ sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['9', '14'])).
% 3.71/3.89  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('17', plain,
% 3.71/3.89      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_B)
% 3.71/3.89         = (k5_relat_1 @ sk_B @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['15', '16'])).
% 3.71/3.89  thf('18', plain,
% 3.71/3.89      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['8', '17'])).
% 3.71/3.89  thf('19', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(t54_relset_1, axiom,
% 3.71/3.89    (![A:$i,B:$i]:
% 3.71/3.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 3.71/3.89       ( ![C:$i]:
% 3.71/3.89         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 3.71/3.89           ( ( ![D:$i]:
% 3.71/3.89               ( ( r2_hidden @ D @ A ) =>
% 3.71/3.89                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 3.71/3.89             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 3.71/3.89  thf('20', plain,
% 3.71/3.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 3.71/3.89          | (r2_relset_1 @ X24 @ X24 @ X25 @ X23)
% 3.71/3.89          | (r2_hidden @ (sk_D @ X23 @ X25 @ X24) @ X24)
% 3.71/3.89          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24))))),
% 3.71/3.89      inference('cnf', [status(esa)], [t54_relset_1])).
% 3.71/3.89  thf('21', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.71/3.89          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 3.71/3.89          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['19', '20'])).
% 3.71/3.89  thf('22', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_B) @ sk_B)
% 3.71/3.89        | (r2_hidden @ (sk_D @ sk_B @ (k5_relat_1 @ sk_B @ sk_B) @ sk_A) @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['18', '21'])).
% 3.71/3.89  thf(d10_xboole_0, axiom,
% 3.71/3.89    (![A:$i,B:$i]:
% 3.71/3.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.71/3.89  thf('23', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.71/3.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.71/3.89  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.71/3.89      inference('simplify', [status(thm)], ['23'])).
% 3.71/3.89  thf(t3_subset, axiom,
% 3.71/3.89    (![A:$i,B:$i]:
% 3.71/3.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.71/3.89  thf('25', plain,
% 3.71/3.89      (![X3 : $i, X5 : $i]:
% 3.71/3.89         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 3.71/3.89      inference('cnf', [status(esa)], [t3_subset])).
% 3.71/3.89  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['24', '25'])).
% 3.71/3.89  thf(t5_subset, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i]:
% 3.71/3.89     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.71/3.89          ( v1_xboole_0 @ C ) ) ))).
% 3.71/3.89  thf('27', plain,
% 3.71/3.89      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.71/3.89         (~ (r2_hidden @ X6 @ X7)
% 3.71/3.89          | ~ (v1_xboole_0 @ X8)
% 3.71/3.89          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 3.71/3.89      inference('cnf', [status(esa)], [t5_subset])).
% 3.71/3.89  thf('28', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['26', '27'])).
% 3.71/3.89  thf('29', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_B) @ sk_B)
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['22', '28'])).
% 3.71/3.89  thf('30', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(t35_funct_2, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i]:
% 3.71/3.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.71/3.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.71/3.89       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.71/3.89         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.71/3.89           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 3.71/3.89             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 3.71/3.89  thf('31', plain,
% 3.71/3.89      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.71/3.89         (((X48) = (k1_xboole_0))
% 3.71/3.89          | ~ (v1_funct_1 @ X49)
% 3.71/3.89          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 3.71/3.89          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 3.71/3.89          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 3.71/3.89          | ~ (v2_funct_1 @ X49)
% 3.71/3.89          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 3.71/3.89      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.71/3.89  thf(redefinition_k6_partfun1, axiom,
% 3.71/3.89    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.71/3.89  thf('32', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.71/3.89  thf('33', plain,
% 3.71/3.89      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.71/3.89         (((X48) = (k1_xboole_0))
% 3.71/3.89          | ~ (v1_funct_1 @ X49)
% 3.71/3.89          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 3.71/3.89          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 3.71/3.89          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_relat_1 @ X50))
% 3.71/3.89          | ~ (v2_funct_1 @ X49)
% 3.71/3.89          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 3.71/3.89      inference('demod', [status(thm)], ['31', '32'])).
% 3.71/3.89  thf('34', plain,
% 3.71/3.89      ((((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 3.71/3.89        | ~ (v2_funct_1 @ sk_B)
% 3.71/3.89        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))
% 3.71/3.89        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | ~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | ((sk_A) = (k1_xboole_0)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['30', '33'])).
% 3.71/3.89  thf('35', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(redefinition_k2_relset_1, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i]:
% 3.71/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.71/3.89       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.71/3.89  thf('36', plain,
% 3.71/3.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.71/3.89         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 3.71/3.89          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.71/3.89  thf('37', plain,
% 3.71/3.89      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['35', '36'])).
% 3.71/3.89  thf('38', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(cc2_funct_2, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i]:
% 3.71/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.71/3.89       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 3.71/3.89         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 3.71/3.89  thf('39', plain,
% 3.71/3.89      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.71/3.89         (~ (v1_funct_1 @ X26)
% 3.71/3.89          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 3.71/3.89          | (v2_funct_2 @ X26 @ X28)
% 3.71/3.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.71/3.89      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.71/3.89  thf('40', plain,
% 3.71/3.89      (((v2_funct_2 @ sk_B @ sk_A)
% 3.71/3.89        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | ~ (v1_funct_1 @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['38', '39'])).
% 3.71/3.89  thf('41', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('43', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 3.71/3.89      inference('demod', [status(thm)], ['40', '41', '42'])).
% 3.71/3.89  thf(d3_funct_2, axiom,
% 3.71/3.89    (![A:$i,B:$i]:
% 3.71/3.89     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.71/3.89       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.71/3.89  thf('44', plain,
% 3.71/3.89      (![X29 : $i, X30 : $i]:
% 3.71/3.89         (~ (v2_funct_2 @ X30 @ X29)
% 3.71/3.89          | ((k2_relat_1 @ X30) = (X29))
% 3.71/3.89          | ~ (v5_relat_1 @ X30 @ X29)
% 3.71/3.89          | ~ (v1_relat_1 @ X30))),
% 3.71/3.89      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.71/3.89  thf('45', plain,
% 3.71/3.89      ((~ (v1_relat_1 @ sk_B)
% 3.71/3.89        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 3.71/3.89        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['43', '44'])).
% 3.71/3.89  thf('46', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(cc1_relset_1, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i]:
% 3.71/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.71/3.89       ( v1_relat_1 @ C ) ))).
% 3.71/3.89  thf('47', plain,
% 3.71/3.89      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.71/3.89         ((v1_relat_1 @ X9)
% 3.71/3.89          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.71/3.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.71/3.89  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 3.71/3.89      inference('sup-', [status(thm)], ['46', '47'])).
% 3.71/3.89  thf('49', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(cc2_relset_1, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i]:
% 3.71/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.71/3.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.71/3.89  thf('50', plain,
% 3.71/3.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.71/3.89         ((v5_relat_1 @ X12 @ X14)
% 3.71/3.89          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.71/3.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.71/3.89  thf('51', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 3.71/3.89      inference('sup-', [status(thm)], ['49', '50'])).
% 3.71/3.89  thf('52', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 3.71/3.89      inference('demod', [status(thm)], ['45', '48', '51'])).
% 3.71/3.89  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 3.71/3.89      inference('demod', [status(thm)], ['37', '52'])).
% 3.71/3.89  thf('54', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('55', plain,
% 3.71/3.89      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.71/3.89         (~ (v1_funct_1 @ X26)
% 3.71/3.89          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 3.71/3.89          | (v2_funct_1 @ X26)
% 3.71/3.89          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.71/3.89      inference('cnf', [status(esa)], [cc2_funct_2])).
% 3.71/3.89  thf('56', plain,
% 3.71/3.89      (((v2_funct_1 @ sk_B)
% 3.71/3.89        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | ~ (v1_funct_1 @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['54', '55'])).
% 3.71/3.89  thf('57', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('59', plain, ((v2_funct_1 @ sk_B)),
% 3.71/3.89      inference('demod', [status(thm)], ['56', '57', '58'])).
% 3.71/3.89  thf('60', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('62', plain,
% 3.71/3.89      ((((sk_A) != (sk_A))
% 3.71/3.89        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))
% 3.71/3.89        | ((sk_A) = (k1_xboole_0)))),
% 3.71/3.89      inference('demod', [status(thm)], ['34', '53', '59', '60', '61'])).
% 3.71/3.89  thf('63', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0))
% 3.71/3.89        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A)))),
% 3.71/3.89      inference('simplify', [status(thm)], ['62'])).
% 3.71/3.89  thf('64', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(dt_k2_funct_2, axiom,
% 3.71/3.89    (![A:$i,B:$i]:
% 3.71/3.89     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.71/3.89         ( v3_funct_2 @ B @ A @ A ) & 
% 3.71/3.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.71/3.89       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 3.71/3.89         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 3.71/3.89         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 3.71/3.89         ( m1_subset_1 @
% 3.71/3.89           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 3.71/3.89  thf('65', plain,
% 3.71/3.89      (![X37 : $i, X38 : $i]:
% 3.71/3.89         ((m1_subset_1 @ (k2_funct_2 @ X37 @ X38) @ 
% 3.71/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 3.71/3.89          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 3.71/3.89          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 3.71/3.89          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 3.71/3.89          | ~ (v1_funct_1 @ X38))),
% 3.71/3.89      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 3.71/3.89  thf('66', plain,
% 3.71/3.89      ((~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 3.71/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['64', '65'])).
% 3.71/3.89  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('68', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('69', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('70', plain,
% 3.71/3.89      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 3.71/3.89  thf('71', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(redefinition_k2_funct_2, axiom,
% 3.71/3.89    (![A:$i,B:$i]:
% 3.71/3.89     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 3.71/3.89         ( v3_funct_2 @ B @ A @ A ) & 
% 3.71/3.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 3.71/3.89       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 3.71/3.89  thf('72', plain,
% 3.71/3.89      (![X45 : $i, X46 : $i]:
% 3.71/3.89         (((k2_funct_2 @ X46 @ X45) = (k2_funct_1 @ X45))
% 3.71/3.89          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))
% 3.71/3.89          | ~ (v3_funct_2 @ X45 @ X46 @ X46)
% 3.71/3.89          | ~ (v1_funct_2 @ X45 @ X46 @ X46)
% 3.71/3.89          | ~ (v1_funct_1 @ X45))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 3.71/3.89  thf('73', plain,
% 3.71/3.89      ((~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['71', '72'])).
% 3.71/3.89  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('75', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('76', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('77', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 3.71/3.89  thf('78', plain,
% 3.71/3.89      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['70', '77'])).
% 3.71/3.89  thf('79', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 3.71/3.89            = (k5_relat_1 @ sk_B @ X0))
% 3.71/3.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.71/3.89          | ~ (v1_funct_1 @ X0))),
% 3.71/3.89      inference('demod', [status(thm)], ['12', '13'])).
% 3.71/3.89  thf('80', plain,
% 3.71/3.89      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 3.71/3.89        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['78', '79'])).
% 3.71/3.89  thf('81', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('82', plain,
% 3.71/3.89      (![X37 : $i, X38 : $i]:
% 3.71/3.89         ((v1_funct_1 @ (k2_funct_2 @ X37 @ X38))
% 3.71/3.89          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 3.71/3.89          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 3.71/3.89          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 3.71/3.89          | ~ (v1_funct_1 @ X38))),
% 3.71/3.89      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 3.71/3.89  thf('83', plain,
% 3.71/3.89      ((~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['81', '82'])).
% 3.71/3.89  thf('84', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('85', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('86', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('87', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 3.71/3.89  thf('88', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 3.71/3.89  thf('89', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['87', '88'])).
% 3.71/3.89  thf('90', plain,
% 3.71/3.89      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('demod', [status(thm)], ['80', '89'])).
% 3.71/3.89  thf('91', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 3.71/3.89  thf('92', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89           (k6_partfun1 @ sk_A))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89             (k6_partfun1 @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('93', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89           (k6_partfun1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('split', [status(esa)], ['92'])).
% 3.71/3.89  thf('94', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.71/3.89  thf('95', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['93', '94'])).
% 3.71/3.89  thf('96', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_1 @ sk_B)) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['91', '95'])).
% 3.71/3.89  thf('97', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['90', '96'])).
% 3.71/3.89  thf('98', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.71/3.89            (k6_relat_1 @ sk_A))
% 3.71/3.89         | ((sk_A) = (k1_xboole_0))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['63', '97'])).
% 3.71/3.89  thf(t29_relset_1, axiom,
% 3.71/3.89    (![A:$i]:
% 3.71/3.89     ( m1_subset_1 @
% 3.71/3.89       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.71/3.89  thf('99', plain,
% 3.71/3.89      (![X22 : $i]:
% 3.71/3.89         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 3.71/3.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 3.71/3.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.71/3.89  thf(redefinition_r2_relset_1, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i,D:$i]:
% 3.71/3.89     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.71/3.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.71/3.89       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.71/3.89  thf('100', plain,
% 3.71/3.89      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.71/3.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.71/3.89          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 3.71/3.89          | ((X18) != (X21)))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.71/3.89  thf('101', plain,
% 3.71/3.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.89         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 3.71/3.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.71/3.89      inference('simplify', [status(thm)], ['100'])).
% 3.71/3.89  thf('102', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['99', '101'])).
% 3.71/3.89  thf('103', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('104', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('105', plain,
% 3.71/3.89      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['70', '77'])).
% 3.71/3.89  thf('106', plain,
% 3.71/3.89      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.71/3.89          | ~ (v1_funct_1 @ X39)
% 3.71/3.89          | ~ (v1_funct_1 @ X42)
% 3.71/3.89          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.71/3.89          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 3.71/3.89              = (k5_relat_1 @ X39 @ X42)))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.71/3.89  thf('107', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 3.71/3.89            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 3.71/3.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.71/3.89          | ~ (v1_funct_1 @ X0)
% 3.71/3.89          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['105', '106'])).
% 3.71/3.89  thf('108', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['87', '88'])).
% 3.71/3.89  thf('109', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 3.71/3.89            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 3.71/3.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.71/3.89          | ~ (v1_funct_1 @ X0))),
% 3.71/3.89      inference('demod', [status(thm)], ['107', '108'])).
% 3.71/3.89  thf('110', plain,
% 3.71/3.89      ((~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 3.71/3.89            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['104', '109'])).
% 3.71/3.89  thf('111', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('112', plain,
% 3.71/3.89      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 3.71/3.89         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['110', '111'])).
% 3.71/3.89  thf('113', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 3.71/3.89  thf('114', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89           (k6_partfun1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('split', [status(esa)], ['92'])).
% 3.71/3.89  thf('115', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.71/3.89  thf('116', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['114', '115'])).
% 3.71/3.89  thf('117', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 3.71/3.89            sk_B) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['113', '116'])).
% 3.71/3.89  thf('118', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['112', '117'])).
% 3.71/3.89  thf('119', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('120', plain,
% 3.71/3.89      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.71/3.89         (((X48) = (k1_xboole_0))
% 3.71/3.89          | ~ (v1_funct_1 @ X49)
% 3.71/3.89          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 3.71/3.89          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 3.71/3.89          | ((k5_relat_1 @ (k2_funct_1 @ X49) @ X49) = (k6_partfun1 @ X48))
% 3.71/3.89          | ~ (v2_funct_1 @ X49)
% 3.71/3.89          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 3.71/3.89      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.71/3.89  thf('121', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.71/3.89  thf('122', plain,
% 3.71/3.89      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.71/3.89         (((X48) = (k1_xboole_0))
% 3.71/3.89          | ~ (v1_funct_1 @ X49)
% 3.71/3.89          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 3.71/3.89          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 3.71/3.89          | ((k5_relat_1 @ (k2_funct_1 @ X49) @ X49) = (k6_relat_1 @ X48))
% 3.71/3.89          | ~ (v2_funct_1 @ X49)
% 3.71/3.89          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 3.71/3.89      inference('demod', [status(thm)], ['120', '121'])).
% 3.71/3.89  thf('123', plain,
% 3.71/3.89      ((((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 3.71/3.89        | ~ (v2_funct_1 @ sk_B)
% 3.71/3.89        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))
% 3.71/3.89        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 3.71/3.89        | ~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | ((sk_A) = (k1_xboole_0)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['119', '122'])).
% 3.71/3.89  thf('124', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 3.71/3.89      inference('demod', [status(thm)], ['37', '52'])).
% 3.71/3.89  thf('125', plain, ((v2_funct_1 @ sk_B)),
% 3.71/3.89      inference('demod', [status(thm)], ['56', '57', '58'])).
% 3.71/3.89  thf('126', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('127', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('128', plain,
% 3.71/3.89      ((((sk_A) != (sk_A))
% 3.71/3.89        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))
% 3.71/3.89        | ((sk_A) = (k1_xboole_0)))),
% 3.71/3.89      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 3.71/3.89  thf('129', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0))
% 3.71/3.89        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A)))),
% 3.71/3.89      inference('simplify', [status(thm)], ['128'])).
% 3.71/3.89  thf('130', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['112', '117'])).
% 3.71/3.89  thf('131', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.71/3.89            (k6_relat_1 @ sk_A))
% 3.71/3.89         | ((sk_A) = (k1_xboole_0))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['129', '130'])).
% 3.71/3.89  thf('132', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['99', '101'])).
% 3.71/3.89  thf('133', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('134', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('135', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('136', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 3.71/3.89           (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['118', '133', '134', '135'])).
% 3.71/3.89  thf('137', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('138', plain,
% 3.71/3.89      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 3.71/3.89  thf('139', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('140', plain,
% 3.71/3.89      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.71/3.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.71/3.89          | ((X18) = (X21))
% 3.71/3.89          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.71/3.89  thf('141', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0)
% 3.71/3.89          | ((sk_B) = (X0))
% 3.71/3.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['139', '140'])).
% 3.71/3.89  thf('142', plain,
% 3.71/3.89      ((((sk_B) = (k2_funct_2 @ sk_A @ sk_B))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_2 @ sk_A @ sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['138', '141'])).
% 3.71/3.89  thf('143', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 3.71/3.89  thf('144', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 3.71/3.89  thf('145', plain,
% 3.71/3.89      ((((sk_B) = (k2_funct_1 @ sk_B))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('demod', [status(thm)], ['142', '143', '144'])).
% 3.71/3.89  thf('146', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89         | ((sk_B) = (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['137', '145'])).
% 3.71/3.89  thf('147', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('148', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ 
% 3.71/3.89            (k2_funct_1 @ sk_B))
% 3.71/3.89         | ((sk_B) = (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['146', '147'])).
% 3.71/3.89  thf('149', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('150', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('151', plain,
% 3.71/3.89      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['70', '77'])).
% 3.71/3.89  thf('152', plain,
% 3.71/3.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 3.71/3.89          | (r2_relset_1 @ X24 @ X24 @ X25 @ X23)
% 3.71/3.89          | (r2_hidden @ (sk_D @ X23 @ X25 @ X24) @ X24)
% 3.71/3.89          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24))))),
% 3.71/3.89      inference('cnf', [status(esa)], [t54_relset_1])).
% 3.71/3.89  thf('153', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.71/3.89          | (r2_hidden @ (sk_D @ (k2_funct_1 @ sk_B) @ X0 @ sk_A) @ sk_A)
% 3.71/3.89          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['151', '152'])).
% 3.71/3.89  thf('154', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89        | (r2_hidden @ (sk_D @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A) @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['150', '153'])).
% 3.71/3.89  thf('155', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['26', '27'])).
% 3.71/3.89  thf('156', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['154', '155'])).
% 3.71/3.89  thf('157', plain,
% 3.71/3.89      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.71/3.89         | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['149', '156'])).
% 3.71/3.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.71/3.89  thf('158', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('159', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('160', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('161', plain,
% 3.71/3.89      (((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ (k2_funct_1 @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 3.71/3.89  thf('162', plain,
% 3.71/3.89      ((((sk_B) = (k2_funct_1 @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['148', '161'])).
% 3.71/3.89  thf('163', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ sk_B @ sk_B) @ (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['136', '162'])).
% 3.71/3.89  thf('164', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('165', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('166', plain,
% 3.71/3.89      (![X22 : $i]:
% 3.71/3.89         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 3.71/3.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 3.71/3.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.71/3.89  thf('167', plain,
% 3.71/3.89      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.71/3.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.71/3.89          | ((X18) = (X21))
% 3.71/3.89          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.71/3.89  thf('168', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]:
% 3.71/3.89         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 3.71/3.89          | ((k6_relat_1 @ X0) = (X1))
% 3.71/3.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['166', '167'])).
% 3.71/3.89  thf('169', plain,
% 3.71/3.89      ((((k6_relat_1 @ sk_A) = (sk_B))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['165', '168'])).
% 3.71/3.89  thf('170', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['164', '169'])).
% 3.71/3.89  thf('171', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('172', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('173', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('174', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89            (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k6_relat_1 @ k1_xboole_0) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 3.71/3.89  thf('175', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('176', plain,
% 3.71/3.89      (![X22 : $i]:
% 3.71/3.89         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 3.71/3.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 3.71/3.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.71/3.89  thf('177', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.71/3.89          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 3.71/3.89          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['19', '20'])).
% 3.71/3.89  thf('178', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.71/3.89        | (r2_hidden @ (sk_D @ sk_B @ (k6_relat_1 @ sk_A) @ sk_A) @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['176', '177'])).
% 3.71/3.89  thf('179', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['26', '27'])).
% 3.71/3.89  thf('180', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['178', '179'])).
% 3.71/3.89  thf('181', plain,
% 3.71/3.89      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.71/3.89         | (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['175', '180'])).
% 3.71/3.89  thf('182', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('183', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('184', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('185', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('186', plain,
% 3.71/3.89      (((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89         (k6_relat_1 @ k1_xboole_0) @ sk_B))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['181', '182', '183', '184', '185'])).
% 3.71/3.89  thf('187', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['174', '186'])).
% 3.71/3.89  thf('188', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['174', '186'])).
% 3.71/3.89  thf('189', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ 
% 3.71/3.89            (k6_relat_1 @ k1_xboole_0)) @ 
% 3.71/3.89           (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['163', '187', '188'])).
% 3.71/3.89  thf('190', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('191', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('192', plain,
% 3.71/3.89      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['70', '77'])).
% 3.71/3.89  thf('193', plain,
% 3.71/3.89      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.71/3.89          | ~ (v1_funct_1 @ X31)
% 3.71/3.89          | ~ (v1_funct_1 @ X34)
% 3.71/3.89          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.71/3.89          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 3.71/3.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 3.71/3.89      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.71/3.89  thf('194', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         ((m1_subset_1 @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ (k2_funct_1 @ sk_B) @ X1) @ 
% 3.71/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.71/3.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.71/3.89          | ~ (v1_funct_1 @ X1)
% 3.71/3.89          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['192', '193'])).
% 3.71/3.89  thf('195', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['87', '88'])).
% 3.71/3.89  thf('196', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.89         ((m1_subset_1 @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ (k2_funct_1 @ sk_B) @ X1) @ 
% 3.71/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.71/3.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.71/3.89          | ~ (v1_funct_1 @ X1))),
% 3.71/3.89      inference('demod', [status(thm)], ['194', '195'])).
% 3.71/3.89  thf('197', plain,
% 3.71/3.89      ((~ (v1_funct_1 @ sk_B)
% 3.71/3.89        | (m1_subset_1 @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 3.71/3.89            sk_B) @ 
% 3.71/3.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['191', '196'])).
% 3.71/3.89  thf('198', plain, ((v1_funct_1 @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('199', plain,
% 3.71/3.89      ((m1_subset_1 @ 
% 3.71/3.89        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['197', '198'])).
% 3.71/3.89  thf('200', plain,
% 3.71/3.89      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 3.71/3.89         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['110', '111'])).
% 3.71/3.89  thf('201', plain,
% 3.71/3.89      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 3.71/3.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['199', '200'])).
% 3.71/3.89  thf('202', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['24', '25'])).
% 3.71/3.89  thf('203', plain,
% 3.71/3.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))
% 3.71/3.89          | (r2_relset_1 @ X24 @ X24 @ X25 @ X23)
% 3.71/3.89          | (r2_hidden @ (sk_D @ X23 @ X25 @ X24) @ X24)
% 3.71/3.89          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24))))),
% 3.71/3.89      inference('cnf', [status(esa)], [t54_relset_1])).
% 3.71/3.89  thf('204', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 3.71/3.89          | (r2_hidden @ (sk_D @ (k2_zfmisc_1 @ X0 @ X0) @ X1 @ X0) @ X0)
% 3.71/3.89          | (r2_relset_1 @ X0 @ X0 @ X1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['202', '203'])).
% 3.71/3.89  thf('205', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 3.71/3.89         (k2_zfmisc_1 @ sk_A @ sk_A))
% 3.71/3.89        | (r2_hidden @ 
% 3.71/3.89           (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ 
% 3.71/3.89            (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A) @ 
% 3.71/3.89           sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['201', '204'])).
% 3.71/3.89  thf('206', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['26', '27'])).
% 3.71/3.89  thf('207', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 3.71/3.89         (k2_zfmisc_1 @ sk_A @ sk_A))
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['205', '206'])).
% 3.71/3.89  thf('208', plain,
% 3.71/3.89      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.71/3.89         | (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89            (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 3.71/3.89            (k2_zfmisc_1 @ sk_A @ sk_A))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['190', '207'])).
% 3.71/3.89  thf('209', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('210', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('211', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('212', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['174', '186'])).
% 3.71/3.89  thf('213', plain,
% 3.71/3.89      ((((sk_B) = (k2_funct_1 @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['148', '161'])).
% 3.71/3.89  thf('214', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['174', '186'])).
% 3.71/3.89  thf('215', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['174', '186'])).
% 3.71/3.89  thf('216', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (k2_funct_1 @ (k6_relat_1 @ k1_xboole_0))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['213', '214', '215'])).
% 3.71/3.89  thf('217', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['174', '186'])).
% 3.71/3.89  thf('218', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('219', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('220', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('221', plain,
% 3.71/3.89      (![X22 : $i]:
% 3.71/3.89         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 3.71/3.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 3.71/3.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.71/3.89  thf('222', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]:
% 3.71/3.89         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 3.71/3.89          | (r2_hidden @ (sk_D @ (k2_zfmisc_1 @ X0 @ X0) @ X1 @ X0) @ X0)
% 3.71/3.89          | (r2_relset_1 @ X0 @ X0 @ X1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['202', '203'])).
% 3.71/3.89  thf('223', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         ((r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 3.71/3.89          | (r2_hidden @ 
% 3.71/3.89             (sk_D @ (k2_zfmisc_1 @ X0 @ X0) @ (k6_relat_1 @ X0) @ X0) @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['221', '222'])).
% 3.71/3.89  thf('224', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['26', '27'])).
% 3.71/3.89  thf('225', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         ((r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 3.71/3.89          | ~ (v1_xboole_0 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['223', '224'])).
% 3.71/3.89  thf('226', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['24', '25'])).
% 3.71/3.89  thf('227', plain,
% 3.71/3.89      (![X0 : $i, X1 : $i]:
% 3.71/3.89         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 3.71/3.89          | ((k6_relat_1 @ X0) = (X1))
% 3.71/3.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['166', '167'])).
% 3.71/3.89  thf('228', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (((k6_relat_1 @ X0) = (k2_zfmisc_1 @ X0 @ X0))
% 3.71/3.89          | ~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ 
% 3.71/3.89               (k2_zfmisc_1 @ X0 @ X0)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['226', '227'])).
% 3.71/3.89  thf('229', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (~ (v1_xboole_0 @ X0) | ((k6_relat_1 @ X0) = (k2_zfmisc_1 @ X0 @ X0)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['225', '228'])).
% 3.71/3.89  thf('230', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('231', plain,
% 3.71/3.89      (![X3 : $i, X4 : $i]:
% 3.71/3.89         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 3.71/3.89      inference('cnf', [status(esa)], [t3_subset])).
% 3.71/3.89  thf('232', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['230', '231'])).
% 3.71/3.89  thf('233', plain,
% 3.71/3.89      (![X0 : $i, X2 : $i]:
% 3.71/3.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.71/3.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.71/3.89  thf('234', plain,
% 3.71/3.89      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B)
% 3.71/3.89        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['232', '233'])).
% 3.71/3.89  thf('235', plain,
% 3.71/3.89      ((~ (r1_tarski @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A)
% 3.71/3.89        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['229', '234'])).
% 3.71/3.89  thf('236', plain,
% 3.71/3.89      (((~ (r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B))
% 3.71/3.89         | ~ (v1_xboole_0 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['220', '235'])).
% 3.71/3.89  thf('237', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('238', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('239', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['131', '132'])).
% 3.71/3.89  thf('240', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('241', plain,
% 3.71/3.89      (((~ (r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['236', '237', '238', '239', '240'])).
% 3.71/3.89  thf('242', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['174', '186'])).
% 3.71/3.89  thf('243', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.71/3.89      inference('simplify', [status(thm)], ['23'])).
% 3.71/3.89  thf('244', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['174', '186'])).
% 3.71/3.89  thf('245', plain,
% 3.71/3.89      ((((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['241', '242', '243', '244'])).
% 3.71/3.89  thf('246', plain,
% 3.71/3.89      (((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89         (k5_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ (k6_relat_1 @ k1_xboole_0)) @ 
% 3.71/3.89         (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)],
% 3.71/3.89                ['208', '209', '210', '211', '212', '216', '217', '218', 
% 3.71/3.89                 '219', '245'])).
% 3.71/3.89  thf('247', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89         (k6_partfun1 @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['189', '246'])).
% 3.71/3.89  thf('248', plain,
% 3.71/3.89      (~
% 3.71/3.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89         (k6_partfun1 @ sk_A))) | 
% 3.71/3.89       ~
% 3.71/3.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89         (k6_partfun1 @ sk_A)))),
% 3.71/3.89      inference('split', [status(esa)], ['92'])).
% 3.71/3.89  thf('249', plain,
% 3.71/3.89      (~
% 3.71/3.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89         (k6_partfun1 @ sk_A)))),
% 3.71/3.89      inference('sat_resolution*', [status(thm)], ['247', '248'])).
% 3.71/3.89  thf('250', plain, (((sk_A) = (k1_xboole_0))),
% 3.71/3.89      inference('simpl_trail', [status(thm)], ['103', '249'])).
% 3.71/3.89  thf('251', plain, (((sk_A) = (k1_xboole_0))),
% 3.71/3.89      inference('simpl_trail', [status(thm)], ['103', '249'])).
% 3.71/3.89  thf('252', plain, (((sk_A) = (k1_xboole_0))),
% 3.71/3.89      inference('simpl_trail', [status(thm)], ['103', '249'])).
% 3.71/3.89  thf('253', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('254', plain,
% 3.71/3.89      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ (k5_relat_1 @ sk_B @ sk_B) @ 
% 3.71/3.89        sk_B)),
% 3.71/3.89      inference('demod', [status(thm)], ['29', '250', '251', '252', '253'])).
% 3.71/3.89  thf('255', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('256', plain,
% 3.71/3.89      ((((k6_relat_1 @ sk_A) = (sk_B))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['165', '168'])).
% 3.71/3.89  thf('257', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['255', '256'])).
% 3.71/3.89  thf('258', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('259', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('260', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('261', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89            (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k6_relat_1 @ k1_xboole_0) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['257', '258', '259', '260'])).
% 3.71/3.89  thf('262', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('263', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['178', '179'])).
% 3.71/3.89  thf('264', plain,
% 3.71/3.89      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.71/3.89         | (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['262', '263'])).
% 3.71/3.89  thf('265', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('266', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('267', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('268', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['98', '102'])).
% 3.71/3.89  thf('269', plain,
% 3.71/3.89      (((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89         (k6_relat_1 @ k1_xboole_0) @ sk_B))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['264', '265', '266', '267', '268'])).
% 3.71/3.89  thf('270', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_partfun1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['261', '269'])).
% 3.71/3.89  thf('271', plain,
% 3.71/3.89      (~
% 3.71/3.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89         (k6_partfun1 @ sk_A)))),
% 3.71/3.89      inference('sat_resolution*', [status(thm)], ['247', '248'])).
% 3.71/3.89  thf('272', plain, (((k6_relat_1 @ k1_xboole_0) = (sk_B))),
% 3.71/3.89      inference('simpl_trail', [status(thm)], ['270', '271'])).
% 3.71/3.89  thf('273', plain, (((k6_relat_1 @ k1_xboole_0) = (sk_B))),
% 3.71/3.89      inference('simpl_trail', [status(thm)], ['270', '271'])).
% 3.71/3.89  thf('274', plain, (((k6_relat_1 @ k1_xboole_0) = (sk_B))),
% 3.71/3.89      inference('simpl_trail', [status(thm)], ['270', '271'])).
% 3.71/3.89  thf('275', plain,
% 3.71/3.89      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89        (k5_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ (k6_relat_1 @ k1_xboole_0)) @ 
% 3.71/3.89        (k6_relat_1 @ k1_xboole_0))),
% 3.71/3.89      inference('demod', [status(thm)], ['254', '272', '273', '274'])).
% 3.71/3.89  thf('276', plain,
% 3.71/3.89      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('demod', [status(thm)], ['80', '89'])).
% 3.71/3.89  thf('277', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 3.71/3.89  thf('278', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89           (k6_partfun1 @ sk_A))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89             (k6_partfun1 @ sk_A)))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('279', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.71/3.89  thf('280', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 3.71/3.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.71/3.89  thf('281', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89             (k6_relat_1 @ sk_A)))),
% 3.71/3.89      inference('demod', [status(thm)], ['278', '279', '280'])).
% 3.71/3.89  thf('282', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('split', [status(esa)], ['281'])).
% 3.71/3.89  thf('283', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89            (k2_funct_1 @ sk_B)) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['277', '282'])).
% 3.71/3.89  thf('284', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['276', '283'])).
% 3.71/3.89  thf('285', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0))
% 3.71/3.89        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A)))),
% 3.71/3.89      inference('simplify', [status(thm)], ['62'])).
% 3.71/3.89  thf('286', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['276', '283'])).
% 3.71/3.89  thf('287', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.71/3.89            (k6_relat_1 @ sk_A))
% 3.71/3.89         | ((sk_A) = (k1_xboole_0))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['285', '286'])).
% 3.71/3.89  thf('288', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['99', '101'])).
% 3.71/3.89  thf('289', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('290', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('291', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('292', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 3.71/3.89           (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['284', '289', '290', '291'])).
% 3.71/3.89  thf('293', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('294', plain,
% 3.71/3.89      ((((sk_B) = (k2_funct_1 @ sk_B))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('demod', [status(thm)], ['142', '143', '144'])).
% 3.71/3.89  thf('295', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89         | ((sk_B) = (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['293', '294'])).
% 3.71/3.89  thf('296', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('297', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ 
% 3.71/3.89            (k2_funct_1 @ sk_B))
% 3.71/3.89         | ((sk_B) = (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['295', '296'])).
% 3.71/3.89  thf('298', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('299', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['154', '155'])).
% 3.71/3.89  thf('300', plain,
% 3.71/3.89      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.71/3.89         | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['298', '299'])).
% 3.71/3.89  thf('301', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('302', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('303', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('304', plain,
% 3.71/3.89      (((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ (k2_funct_1 @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['300', '301', '302', '303'])).
% 3.71/3.89  thf('305', plain,
% 3.71/3.89      ((((sk_B) = (k2_funct_1 @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['297', '304'])).
% 3.71/3.89  thf('306', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ sk_B @ sk_B) @ (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['292', '305'])).
% 3.71/3.89  thf('307', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('308', plain,
% 3.71/3.89      ((((k6_relat_1 @ sk_A) = (sk_B))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['165', '168'])).
% 3.71/3.89  thf('309', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['307', '308'])).
% 3.71/3.89  thf('310', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('311', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('312', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('313', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89            (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k6_relat_1 @ k1_xboole_0) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['309', '310', '311', '312'])).
% 3.71/3.89  thf('314', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('315', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['178', '179'])).
% 3.71/3.89  thf('316', plain,
% 3.71/3.89      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.71/3.89         | (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['314', '315'])).
% 3.71/3.89  thf('317', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('318', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('319', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('320', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['287', '288'])).
% 3.71/3.89  thf('321', plain,
% 3.71/3.89      (((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89         (k6_relat_1 @ k1_xboole_0) @ sk_B))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['316', '317', '318', '319', '320'])).
% 3.71/3.89  thf('322', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['313', '321'])).
% 3.71/3.89  thf('323', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['313', '321'])).
% 3.71/3.89  thf('324', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ 
% 3.71/3.89            (k6_relat_1 @ k1_xboole_0)) @ 
% 3.71/3.89           (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['306', '322', '323'])).
% 3.71/3.89  thf('325', plain,
% 3.71/3.89      (($false)
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['275', '324'])).
% 3.71/3.89  thf('326', plain,
% 3.71/3.89      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89        (k5_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ (k6_relat_1 @ k1_xboole_0)) @ 
% 3.71/3.89        (k6_relat_1 @ k1_xboole_0))),
% 3.71/3.89      inference('demod', [status(thm)], ['254', '272', '273', '274'])).
% 3.71/3.89  thf('327', plain,
% 3.71/3.89      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 3.71/3.89         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['110', '111'])).
% 3.71/3.89  thf('328', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 3.71/3.89      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 3.71/3.89  thf('329', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('split', [status(esa)], ['281'])).
% 3.71/3.89  thf('330', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 3.71/3.89            sk_B) @ 
% 3.71/3.89           (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['328', '329'])).
% 3.71/3.89  thf('331', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['327', '330'])).
% 3.71/3.89  thf('332', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0))
% 3.71/3.89        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A)))),
% 3.71/3.89      inference('simplify', [status(thm)], ['128'])).
% 3.71/3.89  thf('333', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['327', '330'])).
% 3.71/3.89  thf('334', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.71/3.89            (k6_relat_1 @ sk_A))
% 3.71/3.89         | ((sk_A) = (k1_xboole_0))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['332', '333'])).
% 3.71/3.89  thf('335', plain,
% 3.71/3.89      (![X0 : $i]:
% 3.71/3.89         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.71/3.89      inference('sup-', [status(thm)], ['99', '101'])).
% 3.71/3.89  thf('336', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('337', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('338', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('339', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 3.71/3.89           (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['331', '336', '337', '338'])).
% 3.71/3.89  thf('340', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('341', plain,
% 3.71/3.89      ((((sk_B) = (k2_funct_1 @ sk_B))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)))),
% 3.71/3.89      inference('demod', [status(thm)], ['142', '143', '144'])).
% 3.71/3.89  thf('342', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89         | ((sk_B) = (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['340', '341'])).
% 3.71/3.89  thf('343', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('344', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ 
% 3.71/3.89            (k2_funct_1 @ sk_B))
% 3.71/3.89         | ((sk_B) = (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['342', '343'])).
% 3.71/3.89  thf('345', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('346', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['154', '155'])).
% 3.71/3.89  thf('347', plain,
% 3.71/3.89      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.71/3.89         | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['345', '346'])).
% 3.71/3.89  thf('348', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('349', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('350', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('351', plain,
% 3.71/3.89      (((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ (k2_funct_1 @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['347', '348', '349', '350'])).
% 3.71/3.89  thf('352', plain,
% 3.71/3.89      ((((sk_B) = (k2_funct_1 @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['344', '351'])).
% 3.71/3.89  thf('353', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ sk_B @ sk_B) @ (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['339', '352'])).
% 3.71/3.89  thf('354', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('355', plain,
% 3.71/3.89      ((((k6_relat_1 @ sk_A) = (sk_B))
% 3.71/3.89        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['165', '168'])).
% 3.71/3.89  thf('356', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k6_relat_1 @ sk_A) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['354', '355'])).
% 3.71/3.89  thf('357', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('358', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('359', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('360', plain,
% 3.71/3.89      (((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89            (k6_relat_1 @ k1_xboole_0) @ sk_B)
% 3.71/3.89         | ((k6_relat_1 @ k1_xboole_0) = (sk_B))))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['356', '357', '358', '359'])).
% 3.71/3.89  thf('361', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('362', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.71/3.89        | ~ (v1_xboole_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['178', '179'])).
% 3.71/3.89  thf('363', plain,
% 3.71/3.89      (((~ (v1_xboole_0 @ k1_xboole_0)
% 3.71/3.89         | (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('sup-', [status(thm)], ['361', '362'])).
% 3.71/3.89  thf('364', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.71/3.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.71/3.89  thf('365', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('366', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('367', plain,
% 3.71/3.89      ((((sk_A) = (k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['334', '335'])).
% 3.71/3.89  thf('368', plain,
% 3.71/3.89      (((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89         (k6_relat_1 @ k1_xboole_0) @ sk_B))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['363', '364', '365', '366', '367'])).
% 3.71/3.89  thf('369', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['360', '368'])).
% 3.71/3.89  thf('370', plain,
% 3.71/3.89      ((((k6_relat_1 @ k1_xboole_0) = (sk_B)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['360', '368'])).
% 3.71/3.89  thf('371', plain,
% 3.71/3.89      ((~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.71/3.89           (k5_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ 
% 3.71/3.89            (k6_relat_1 @ k1_xboole_0)) @ 
% 3.71/3.89           (k6_relat_1 @ k1_xboole_0)))
% 3.71/3.89         <= (~
% 3.71/3.89             ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89               (k6_relat_1 @ sk_A))))),
% 3.71/3.89      inference('demod', [status(thm)], ['353', '369', '370'])).
% 3.71/3.89  thf('372', plain,
% 3.71/3.89      (((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89         (k6_relat_1 @ sk_A)))),
% 3.71/3.89      inference('sup-', [status(thm)], ['326', '371'])).
% 3.71/3.89  thf('373', plain,
% 3.71/3.89      (~
% 3.71/3.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89         (k6_relat_1 @ sk_A))) | 
% 3.71/3.89       ~
% 3.71/3.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 3.71/3.89         (k6_relat_1 @ sk_A)))),
% 3.71/3.89      inference('split', [status(esa)], ['281'])).
% 3.71/3.89  thf('374', plain,
% 3.71/3.89      (~
% 3.71/3.89       ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.71/3.89         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 3.71/3.89          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 3.71/3.89         (k6_relat_1 @ sk_A)))),
% 3.71/3.89      inference('sat_resolution*', [status(thm)], ['372', '373'])).
% 3.71/3.89  thf('375', plain, ($false),
% 3.71/3.89      inference('simpl_trail', [status(thm)], ['325', '374'])).
% 3.71/3.89  
% 3.71/3.89  % SZS output end Refutation
% 3.71/3.89  
% 3.71/3.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
