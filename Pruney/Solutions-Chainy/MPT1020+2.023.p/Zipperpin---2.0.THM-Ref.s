%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HAHzLGjdjM

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:04 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  206 (1615 expanded)
%              Number of leaves         :   59 ( 500 expanded)
%              Depth                    :   19
%              Number of atoms          : 1813 (39127 expanded)
%              Number of equality atoms :   87 ( 481 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X53: $i,X54: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X53 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X53 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X53 ) ) )
      | ~ ( v3_funct_2 @ X54 @ X53 @ X53 )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X53 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k2_funct_2 @ X56 @ X55 )
        = ( k2_funct_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X56 ) ) )
      | ~ ( v3_funct_2 @ X55 @ X56 @ X56 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X56 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ X16 )
        = ( k4_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v3_funct_2 @ X42 @ X43 @ X44 )
      | ( v2_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('21',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','10','11','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4','5','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('29',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) )
      | ( r2_relset_1 @ X40 @ X40 @ X41 @ X39 )
      | ( r2_hidden @ ( sk_D @ X39 @ X41 @ X40 ) @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4','5','26'])).

thf(symmetry_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
       => ( r2_relset_1 @ A @ B @ D @ C ) ) ) )).

thf('34',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( r2_relset_1 @ X32 @ X33 @ X34 @ X31 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r2_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) @ X0 )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k4_relat_1 @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','10','11','25'])).

thf('39',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k4_relat_1 @ sk_B ) @ sk_C ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_D @ sk_C @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['31','40'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('45',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('59',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('60',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('62',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_funct_2 @ X62 @ X63 @ X64 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) )
      | ( X62
        = ( k2_funct_1 @ X65 ) )
      | ~ ( r2_relset_1 @ X64 @ X64 @ ( k1_partfun1 @ X64 @ X63 @ X63 @ X64 @ X65 @ X62 ) @ ( k6_partfun1 @ X64 ) )
      | ( X63 = k1_xboole_0 )
      | ( X64 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X65 )
      | ( ( k2_relset_1 @ X64 @ X63 @ X65 )
       != X63 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X63 ) ) )
      | ~ ( v1_funct_2 @ X65 @ X64 @ X63 )
      | ~ ( v1_funct_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('63',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_funct_2 @ X62 @ X63 @ X64 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) )
      | ( X62
        = ( k2_funct_1 @ X65 ) )
      | ~ ( r2_relset_1 @ X64 @ X64 @ ( k1_partfun1 @ X64 @ X63 @ X63 @ X64 @ X65 @ X62 ) @ ( k6_relat_1 @ X64 ) )
      | ( X63 = k1_xboole_0 )
      | ( X64 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X65 )
      | ( ( k2_relset_1 @ X64 @ X63 @ X65 )
       != X63 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X63 ) ) )
      | ~ ( v1_funct_2 @ X65 @ X64 @ X63 )
      | ~ ( v1_funct_1 @ X65 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('72',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 )
      | ( X27 != X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('73',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('79',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v3_funct_2 @ X42 @ X43 @ X44 )
      | ( v2_funct_2 @ X42 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('83',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['83','84','85'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('87',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v2_funct_2 @ X46 @ X45 )
      | ( ( k2_relat_1 @ X46 )
        = X45 )
      | ~ ( v5_relat_1 @ X46 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('91',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('92',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['88','89','92'])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['80','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('96',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('97',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','74','75','76','77','94','95','96'])).

thf('98',plain,
    ( ( sk_C
      = ( k4_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('100',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_relset_1 @ X28 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('103',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('107',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ X35 ) @ ( k2_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[t19_relset_1])).

thf('108',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('110',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['108','109'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('111',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('112',plain,
    ( ( k4_xboole_0 @ ( k3_relat_1 @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','111'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('113',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('114',plain,
    ( ( k1_xboole_0
     != ( k3_relat_1 @ sk_B ) )
    | ( r1_xboole_0 @ ( k3_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['88','89','92'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('116',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('117',plain,
    ( ( ( k3_relat_1 @ sk_B )
      = ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('120',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['118','119'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('121',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('122',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('124',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['122','123'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('125',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('126',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('128',plain,
    ( ( k3_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['117','126','127'])).

thf('129',plain,
    ( ( k3_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['117','126','127'])).

thf('130',plain,
    ( ( k1_xboole_0 != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['114','128','129'])).

thf('131',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('132',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('133',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('134',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['134'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('136',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('137',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['108','109'])).

thf('139',plain,
    ( ( k3_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['117','126','127'])).

thf('140',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('142',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','103'])).

thf('143',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['137','143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['105','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HAHzLGjdjM
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.96/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.96/1.15  % Solved by: fo/fo7.sh
% 0.96/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.15  % done 1276 iterations in 0.705s
% 0.96/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.96/1.15  % SZS output start Refutation
% 0.96/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.96/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.96/1.15  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.96/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.15  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.96/1.15  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.96/1.15  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.96/1.15  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.96/1.15  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.96/1.15  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.96/1.15  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.96/1.15  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.96/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.96/1.15  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.96/1.15  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.96/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.96/1.15  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.96/1.15  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.96/1.15  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.96/1.15  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.96/1.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.96/1.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.96/1.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.96/1.15  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.96/1.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.96/1.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.96/1.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.96/1.15  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.96/1.15  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.96/1.15  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.96/1.15  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.96/1.15  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.96/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.96/1.15  thf(sk_C_type, type, sk_C: $i).
% 0.96/1.15  thf(t87_funct_2, conjecture,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.96/1.15         ( v3_funct_2 @ B @ A @ A ) & 
% 0.96/1.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.96/1.15       ( ![C:$i]:
% 0.96/1.15         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.96/1.15             ( v3_funct_2 @ C @ A @ A ) & 
% 0.96/1.15             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.96/1.15           ( ( r2_relset_1 @
% 0.96/1.15               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.96/1.15               ( k6_partfun1 @ A ) ) =>
% 0.96/1.15             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.96/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.15    (~( ![A:$i,B:$i]:
% 0.96/1.15        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.96/1.15            ( v3_funct_2 @ B @ A @ A ) & 
% 0.96/1.15            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.96/1.15          ( ![C:$i]:
% 0.96/1.15            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.96/1.15                ( v3_funct_2 @ C @ A @ A ) & 
% 0.96/1.15                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.96/1.15              ( ( r2_relset_1 @
% 0.96/1.15                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.96/1.15                  ( k6_partfun1 @ A ) ) =>
% 0.96/1.15                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.96/1.15    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.96/1.15  thf('0', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(dt_k2_funct_2, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.96/1.15         ( v3_funct_2 @ B @ A @ A ) & 
% 0.96/1.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.96/1.15       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.96/1.15         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.96/1.15         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.96/1.15         ( m1_subset_1 @
% 0.96/1.15           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.96/1.15  thf('1', plain,
% 0.96/1.15      (![X53 : $i, X54 : $i]:
% 0.96/1.15         ((m1_subset_1 @ (k2_funct_2 @ X53 @ X54) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X53)))
% 0.96/1.15          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X53)))
% 0.96/1.15          | ~ (v3_funct_2 @ X54 @ X53 @ X53)
% 0.96/1.15          | ~ (v1_funct_2 @ X54 @ X53 @ X53)
% 0.96/1.15          | ~ (v1_funct_1 @ X54))),
% 0.96/1.15      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.96/1.15  thf('2', plain,
% 0.96/1.15      ((~ (v1_funct_1 @ sk_B)
% 0.96/1.15        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.96/1.15        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.96/1.15        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['0', '1'])).
% 0.96/1.15  thf('3', plain, ((v1_funct_1 @ sk_B)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('4', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('5', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('6', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(redefinition_k2_funct_2, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.96/1.15         ( v3_funct_2 @ B @ A @ A ) & 
% 0.96/1.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.96/1.15       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.96/1.15  thf('7', plain,
% 0.96/1.15      (![X55 : $i, X56 : $i]:
% 0.96/1.15         (((k2_funct_2 @ X56 @ X55) = (k2_funct_1 @ X55))
% 0.96/1.15          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X56)))
% 0.96/1.15          | ~ (v3_funct_2 @ X55 @ X56 @ X56)
% 0.96/1.15          | ~ (v1_funct_2 @ X55 @ X56 @ X56)
% 0.96/1.15          | ~ (v1_funct_1 @ X55))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.96/1.15  thf('8', plain,
% 0.96/1.15      ((~ (v1_funct_1 @ sk_B)
% 0.96/1.15        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.96/1.15        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.96/1.15        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['6', '7'])).
% 0.96/1.15  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('10', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('11', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(d9_funct_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.96/1.15       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.96/1.15  thf('13', plain,
% 0.96/1.15      (![X16 : $i]:
% 0.96/1.15         (~ (v2_funct_1 @ X16)
% 0.96/1.15          | ((k2_funct_1 @ X16) = (k4_relat_1 @ X16))
% 0.96/1.15          | ~ (v1_funct_1 @ X16)
% 0.96/1.15          | ~ (v1_relat_1 @ X16))),
% 0.96/1.15      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.96/1.15  thf('14', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ sk_B)
% 0.96/1.15        | ((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))
% 0.96/1.15        | ~ (v2_funct_1 @ sk_B))),
% 0.96/1.15      inference('sup-', [status(thm)], ['12', '13'])).
% 0.96/1.15  thf('15', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(cc1_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.15       ( v1_relat_1 @ C ) ))).
% 0.96/1.15  thf('16', plain,
% 0.96/1.15      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.96/1.15         ((v1_relat_1 @ X18)
% 0.96/1.15          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.96/1.15  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.96/1.15      inference('sup-', [status(thm)], ['15', '16'])).
% 0.96/1.15  thf('18', plain,
% 0.96/1.15      ((((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B)) | ~ (v2_funct_1 @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['14', '17'])).
% 0.96/1.15  thf('19', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(cc2_funct_2, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.15       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.96/1.15         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.96/1.15  thf('20', plain,
% 0.96/1.15      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X42)
% 0.96/1.15          | ~ (v3_funct_2 @ X42 @ X43 @ X44)
% 0.96/1.15          | (v2_funct_1 @ X42)
% 0.96/1.15          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.96/1.15  thf('21', plain,
% 0.96/1.15      (((v2_funct_1 @ sk_B)
% 0.96/1.15        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.96/1.15        | ~ (v1_funct_1 @ sk_B))),
% 0.96/1.15      inference('sup-', [status(thm)], ['19', '20'])).
% 0.96/1.15  thf('22', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('24', plain, ((v2_funct_1 @ sk_B)),
% 0.96/1.15      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.96/1.15  thf('25', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['18', '24'])).
% 0.96/1.15  thf('26', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['8', '9', '10', '11', '25'])).
% 0.96/1.15  thf('27', plain,
% 0.96/1.15      ((m1_subset_1 @ (k4_relat_1 @ sk_B) @ 
% 0.96/1.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('demod', [status(thm)], ['2', '3', '4', '5', '26'])).
% 0.96/1.15  thf('28', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(t54_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.96/1.15       ( ![C:$i]:
% 0.96/1.15         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.96/1.15           ( ( ![D:$i]:
% 0.96/1.15               ( ( r2_hidden @ D @ A ) =>
% 0.96/1.15                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.96/1.15             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.96/1.15  thf('29', plain,
% 0.96/1.15      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 0.96/1.15          | (r2_relset_1 @ X40 @ X40 @ X41 @ X39)
% 0.96/1.15          | (r2_hidden @ (sk_D @ X39 @ X41 @ X40) @ X40)
% 0.96/1.15          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40))))),
% 0.96/1.15      inference('cnf', [status(esa)], [t54_relset_1])).
% 0.96/1.15  thf('30', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.96/1.15          | (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_A)
% 0.96/1.15          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['28', '29'])).
% 0.96/1.15  thf('31', plain,
% 0.96/1.15      (((r2_relset_1 @ sk_A @ sk_A @ (k4_relat_1 @ sk_B) @ sk_C)
% 0.96/1.15        | (r2_hidden @ (sk_D @ sk_C @ (k4_relat_1 @ sk_B) @ sk_A) @ sk_A))),
% 0.96/1.15      inference('sup-', [status(thm)], ['27', '30'])).
% 0.96/1.15  thf('32', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('33', plain,
% 0.96/1.15      ((m1_subset_1 @ (k4_relat_1 @ sk_B) @ 
% 0.96/1.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('demod', [status(thm)], ['2', '3', '4', '5', '26'])).
% 0.96/1.15  thf(symmetry_r2_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.96/1.15     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.96/1.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.96/1.15       ( ( r2_relset_1 @ A @ B @ C @ D ) => ( r2_relset_1 @ A @ B @ D @ C ) ) ))).
% 0.96/1.15  thf('34', plain,
% 0.96/1.15      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.96/1.15          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.96/1.15          | (r2_relset_1 @ X32 @ X33 @ X34 @ X31)
% 0.96/1.15          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 0.96/1.15      inference('cnf', [status(esa)], [symmetry_r2_relset_1])).
% 0.96/1.15  thf('35', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (r2_relset_1 @ sk_A @ sk_A @ (k4_relat_1 @ sk_B) @ X0)
% 0.96/1.15          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ (k4_relat_1 @ sk_B))
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['33', '34'])).
% 0.96/1.15  thf('36', plain,
% 0.96/1.15      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k4_relat_1 @ sk_B))
% 0.96/1.15        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k4_relat_1 @ sk_B) @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['32', '35'])).
% 0.96/1.15  thf('37', plain,
% 0.96/1.15      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('38', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['8', '9', '10', '11', '25'])).
% 0.96/1.15  thf('39', plain,
% 0.96/1.15      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k4_relat_1 @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['37', '38'])).
% 0.96/1.15  thf('40', plain,
% 0.96/1.15      (~ (r2_relset_1 @ sk_A @ sk_A @ (k4_relat_1 @ sk_B) @ sk_C)),
% 0.96/1.15      inference('clc', [status(thm)], ['36', '39'])).
% 0.96/1.15  thf('41', plain,
% 0.96/1.15      ((r2_hidden @ (sk_D @ sk_C @ (k4_relat_1 @ sk_B) @ sk_A) @ sk_A)),
% 0.96/1.15      inference('clc', [status(thm)], ['31', '40'])).
% 0.96/1.15  thf(t7_boole, axiom,
% 0.96/1.15    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.96/1.15  thf('42', plain,
% 0.96/1.15      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.96/1.15      inference('cnf', [status(esa)], [t7_boole])).
% 0.96/1.15  thf('43', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.96/1.15      inference('sup-', [status(thm)], ['41', '42'])).
% 0.96/1.15  thf('44', plain,
% 0.96/1.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.96/1.15        (k6_partfun1 @ sk_A))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(redefinition_k6_partfun1, axiom,
% 0.96/1.15    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.96/1.15  thf('45', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.96/1.15  thf('46', plain,
% 0.96/1.15      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.96/1.15        (k6_relat_1 @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['44', '45'])).
% 0.96/1.15  thf('47', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('48', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(dt_k1_partfun1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ E ) & 
% 0.96/1.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.96/1.15         ( v1_funct_1 @ F ) & 
% 0.96/1.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.96/1.15       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.96/1.15         ( m1_subset_1 @
% 0.96/1.15           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.96/1.15           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.96/1.15  thf('49', plain,
% 0.96/1.15      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.96/1.15          | ~ (v1_funct_1 @ X47)
% 0.96/1.15          | ~ (v1_funct_1 @ X50)
% 0.96/1.15          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.96/1.15          | (m1_subset_1 @ (k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50) @ 
% 0.96/1.15             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X52))))),
% 0.96/1.15      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.96/1.15  thf('50', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.15         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.96/1.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.96/1.15          | ~ (v1_funct_1 @ X1)
% 0.96/1.15          | ~ (v1_funct_1 @ sk_B))),
% 0.96/1.15      inference('sup-', [status(thm)], ['48', '49'])).
% 0.96/1.15  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('52', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.15         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.96/1.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.96/1.15          | ~ (v1_funct_1 @ X1))),
% 0.96/1.15      inference('demod', [status(thm)], ['50', '51'])).
% 0.96/1.15  thf('53', plain,
% 0.96/1.15      ((~ (v1_funct_1 @ sk_C)
% 0.96/1.15        | (m1_subset_1 @ 
% 0.96/1.15           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['47', '52'])).
% 0.96/1.15  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('55', plain,
% 0.96/1.15      ((m1_subset_1 @ 
% 0.96/1.15        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.96/1.15        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('demod', [status(thm)], ['53', '54'])).
% 0.96/1.15  thf(redefinition_r2_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.96/1.15     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.96/1.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.96/1.15       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.96/1.15  thf('56', plain,
% 0.96/1.15      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.96/1.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.96/1.15          | ((X27) = (X30))
% 0.96/1.15          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.96/1.15  thf('57', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.96/1.15          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.96/1.15      inference('sup-', [status(thm)], ['55', '56'])).
% 0.96/1.15  thf('58', plain,
% 0.96/1.15      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.96/1.15           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.96/1.15        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.96/1.15            = (k6_relat_1 @ sk_A)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['46', '57'])).
% 0.96/1.15  thf(t29_relset_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( m1_subset_1 @
% 0.96/1.15       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.96/1.15  thf('59', plain,
% 0.96/1.15      (![X38 : $i]:
% 0.96/1.15         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 0.96/1.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 0.96/1.15      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.96/1.15  thf('60', plain,
% 0.96/1.15      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.96/1.15         = (k6_relat_1 @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['58', '59'])).
% 0.96/1.15  thf('61', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(t36_funct_2, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.96/1.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.96/1.15       ( ![D:$i]:
% 0.96/1.15         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.96/1.15             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.96/1.15           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.96/1.15               ( r2_relset_1 @
% 0.96/1.15                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.96/1.15                 ( k6_partfun1 @ A ) ) & 
% 0.96/1.15               ( v2_funct_1 @ C ) ) =>
% 0.96/1.15             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.96/1.15               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.96/1.15  thf('62', plain,
% 0.96/1.15      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X62)
% 0.96/1.15          | ~ (v1_funct_2 @ X62 @ X63 @ X64)
% 0.96/1.15          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64)))
% 0.96/1.15          | ((X62) = (k2_funct_1 @ X65))
% 0.96/1.15          | ~ (r2_relset_1 @ X64 @ X64 @ 
% 0.96/1.15               (k1_partfun1 @ X64 @ X63 @ X63 @ X64 @ X65 @ X62) @ 
% 0.96/1.15               (k6_partfun1 @ X64))
% 0.96/1.15          | ((X63) = (k1_xboole_0))
% 0.96/1.15          | ((X64) = (k1_xboole_0))
% 0.96/1.15          | ~ (v2_funct_1 @ X65)
% 0.96/1.15          | ((k2_relset_1 @ X64 @ X63 @ X65) != (X63))
% 0.96/1.15          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X63)))
% 0.96/1.15          | ~ (v1_funct_2 @ X65 @ X64 @ X63)
% 0.96/1.15          | ~ (v1_funct_1 @ X65))),
% 0.96/1.15      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.96/1.15  thf('63', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.96/1.15  thf('64', plain,
% 0.96/1.15      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X62)
% 0.96/1.15          | ~ (v1_funct_2 @ X62 @ X63 @ X64)
% 0.96/1.15          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64)))
% 0.96/1.15          | ((X62) = (k2_funct_1 @ X65))
% 0.96/1.15          | ~ (r2_relset_1 @ X64 @ X64 @ 
% 0.96/1.15               (k1_partfun1 @ X64 @ X63 @ X63 @ X64 @ X65 @ X62) @ 
% 0.96/1.15               (k6_relat_1 @ X64))
% 0.96/1.15          | ((X63) = (k1_xboole_0))
% 0.96/1.15          | ((X64) = (k1_xboole_0))
% 0.96/1.15          | ~ (v2_funct_1 @ X65)
% 0.96/1.15          | ((k2_relset_1 @ X64 @ X63 @ X65) != (X63))
% 0.96/1.15          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X63)))
% 0.96/1.15          | ~ (v1_funct_2 @ X65 @ X64 @ X63)
% 0.96/1.15          | ~ (v1_funct_1 @ X65))),
% 0.96/1.15      inference('demod', [status(thm)], ['62', '63'])).
% 0.96/1.15  thf('65', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.96/1.15          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ((sk_A) = (k1_xboole_0))
% 0.96/1.15          | ((sk_A) = (k1_xboole_0))
% 0.96/1.15          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.96/1.15               (k6_relat_1 @ sk_A))
% 0.96/1.15          | ((sk_C) = (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.96/1.15          | ~ (v1_funct_1 @ sk_C))),
% 0.96/1.15      inference('sup-', [status(thm)], ['61', '64'])).
% 0.96/1.15  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('68', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X0)
% 0.96/1.15          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.96/1.15          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ((sk_A) = (k1_xboole_0))
% 0.96/1.15          | ((sk_A) = (k1_xboole_0))
% 0.96/1.15          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.96/1.15               (k6_relat_1 @ sk_A))
% 0.96/1.15          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.96/1.15      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.96/1.15  thf('69', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (((sk_C) = (k2_funct_1 @ X0))
% 0.96/1.15          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.96/1.15               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.96/1.15               (k6_relat_1 @ sk_A))
% 0.96/1.15          | ((sk_A) = (k1_xboole_0))
% 0.96/1.15          | ~ (v2_funct_1 @ X0)
% 0.96/1.15          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.96/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.96/1.15          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.96/1.15          | ~ (v1_funct_1 @ X0))),
% 0.96/1.15      inference('simplify', [status(thm)], ['68'])).
% 0.96/1.15  thf('70', plain,
% 0.96/1.15      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.96/1.15           (k6_relat_1 @ sk_A))
% 0.96/1.15        | ~ (v1_funct_1 @ sk_B)
% 0.96/1.15        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.96/1.15        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.96/1.15        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.96/1.15        | ~ (v2_funct_1 @ sk_B)
% 0.96/1.15        | ((sk_A) = (k1_xboole_0))
% 0.96/1.15        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['60', '69'])).
% 0.96/1.15  thf('71', plain,
% 0.96/1.15      (![X38 : $i]:
% 0.96/1.15         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 0.96/1.15          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 0.96/1.15      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.96/1.15  thf('72', plain,
% 0.96/1.15      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.96/1.15         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.96/1.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.96/1.15          | (r2_relset_1 @ X28 @ X29 @ X27 @ X30)
% 0.96/1.15          | ((X27) != (X30)))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.96/1.15  thf('73', plain,
% 0.96/1.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.96/1.15         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 0.96/1.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.96/1.15      inference('simplify', [status(thm)], ['72'])).
% 0.96/1.15  thf('74', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.96/1.15      inference('sup-', [status(thm)], ['71', '73'])).
% 0.96/1.15  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('76', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('77', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('78', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(redefinition_k2_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.15       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.96/1.15  thf('79', plain,
% 0.96/1.15      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.96/1.15         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.96/1.15          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.96/1.15      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.96/1.15  thf('80', plain,
% 0.96/1.15      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.96/1.15      inference('sup-', [status(thm)], ['78', '79'])).
% 0.96/1.15  thf('81', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('82', plain,
% 0.96/1.15      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.96/1.15         (~ (v1_funct_1 @ X42)
% 0.96/1.15          | ~ (v3_funct_2 @ X42 @ X43 @ X44)
% 0.96/1.15          | (v2_funct_2 @ X42 @ X44)
% 0.96/1.15          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.96/1.15  thf('83', plain,
% 0.96/1.15      (((v2_funct_2 @ sk_B @ sk_A)
% 0.96/1.15        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.96/1.15        | ~ (v1_funct_1 @ sk_B))),
% 0.96/1.15      inference('sup-', [status(thm)], ['81', '82'])).
% 0.96/1.15  thf('84', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('85', plain, ((v1_funct_1 @ sk_B)),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('86', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.96/1.15      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.96/1.15  thf(d3_funct_2, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.96/1.15       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.96/1.15  thf('87', plain,
% 0.96/1.15      (![X45 : $i, X46 : $i]:
% 0.96/1.15         (~ (v2_funct_2 @ X46 @ X45)
% 0.96/1.15          | ((k2_relat_1 @ X46) = (X45))
% 0.96/1.15          | ~ (v5_relat_1 @ X46 @ X45)
% 0.96/1.15          | ~ (v1_relat_1 @ X46))),
% 0.96/1.15      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.96/1.15  thf('88', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ sk_B)
% 0.96/1.15        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.96/1.15        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['86', '87'])).
% 0.96/1.15  thf('89', plain, ((v1_relat_1 @ sk_B)),
% 0.96/1.15      inference('sup-', [status(thm)], ['15', '16'])).
% 0.96/1.15  thf('90', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(cc2_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.15       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.96/1.15  thf('91', plain,
% 0.96/1.15      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.96/1.15         ((v5_relat_1 @ X21 @ X23)
% 0.96/1.15          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.96/1.15  thf('92', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.96/1.15      inference('sup-', [status(thm)], ['90', '91'])).
% 0.96/1.15  thf('93', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['88', '89', '92'])).
% 0.96/1.15  thf('94', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['80', '93'])).
% 0.96/1.15  thf('95', plain, ((v2_funct_1 @ sk_B)),
% 0.96/1.15      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.96/1.15  thf('96', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['18', '24'])).
% 0.96/1.15  thf('97', plain,
% 0.96/1.15      ((((sk_A) != (sk_A))
% 0.96/1.15        | ((sk_A) = (k1_xboole_0))
% 0.96/1.15        | ((sk_C) = (k4_relat_1 @ sk_B)))),
% 0.96/1.15      inference('demod', [status(thm)],
% 0.96/1.15                ['70', '74', '75', '76', '77', '94', '95', '96'])).
% 0.96/1.15  thf('98', plain,
% 0.96/1.15      ((((sk_C) = (k4_relat_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.96/1.15      inference('simplify', [status(thm)], ['97'])).
% 0.96/1.15  thf('99', plain,
% 0.96/1.15      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k4_relat_1 @ sk_B))),
% 0.96/1.15      inference('demod', [status(thm)], ['37', '38'])).
% 0.96/1.15  thf('100', plain,
% 0.96/1.15      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['98', '99'])).
% 0.96/1.15  thf('101', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('102', plain,
% 0.96/1.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.96/1.15         ((r2_relset_1 @ X28 @ X29 @ X30 @ X30)
% 0.96/1.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.96/1.15      inference('simplify', [status(thm)], ['72'])).
% 0.96/1.15  thf('103', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.96/1.15      inference('sup-', [status(thm)], ['101', '102'])).
% 0.96/1.15  thf('104', plain, (((sk_A) = (k1_xboole_0))),
% 0.96/1.15      inference('demod', [status(thm)], ['100', '103'])).
% 0.96/1.15  thf('105', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.96/1.15      inference('demod', [status(thm)], ['43', '104'])).
% 0.96/1.15  thf('106', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(t19_relset_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.96/1.15       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.96/1.15  thf('107', plain,
% 0.96/1.15      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.96/1.15         ((r1_tarski @ (k3_relat_1 @ X35) @ (k2_xboole_0 @ X36 @ X37))
% 0.96/1.15          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.96/1.15      inference('cnf', [status(esa)], [t19_relset_1])).
% 0.96/1.15  thf('108', plain,
% 0.96/1.15      ((r1_tarski @ (k3_relat_1 @ sk_B) @ (k2_xboole_0 @ sk_A @ sk_A))),
% 0.96/1.15      inference('sup-', [status(thm)], ['106', '107'])).
% 0.96/1.15  thf(idempotence_k2_xboole_0, axiom,
% 0.96/1.15    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.96/1.15  thf('109', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.96/1.15      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.96/1.15  thf('110', plain, ((r1_tarski @ (k3_relat_1 @ sk_B) @ sk_A)),
% 0.96/1.15      inference('demod', [status(thm)], ['108', '109'])).
% 0.96/1.15  thf(t37_xboole_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.96/1.15  thf('111', plain,
% 0.96/1.15      (![X3 : $i, X5 : $i]:
% 0.96/1.15         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.96/1.15      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.96/1.15  thf('112', plain,
% 0.96/1.15      (((k4_xboole_0 @ (k3_relat_1 @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.96/1.15      inference('sup-', [status(thm)], ['110', '111'])).
% 0.96/1.15  thf(t83_xboole_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.96/1.15  thf('113', plain,
% 0.96/1.15      (![X10 : $i, X12 : $i]:
% 0.96/1.15         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.96/1.15      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.96/1.15  thf('114', plain,
% 0.96/1.15      ((((k1_xboole_0) != (k3_relat_1 @ sk_B))
% 0.96/1.15        | (r1_xboole_0 @ (k3_relat_1 @ sk_B) @ sk_A))),
% 0.96/1.15      inference('sup-', [status(thm)], ['112', '113'])).
% 0.96/1.15  thf('115', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['88', '89', '92'])).
% 0.96/1.15  thf(d6_relat_1, axiom,
% 0.96/1.15    (![A:$i]:
% 0.96/1.15     ( ( v1_relat_1 @ A ) =>
% 0.96/1.15       ( ( k3_relat_1 @ A ) =
% 0.96/1.15         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.96/1.15  thf('116', plain,
% 0.96/1.15      (![X15 : $i]:
% 0.96/1.15         (((k3_relat_1 @ X15)
% 0.96/1.15            = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.96/1.15          | ~ (v1_relat_1 @ X15))),
% 0.96/1.15      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.96/1.15  thf('117', plain,
% 0.96/1.15      ((((k3_relat_1 @ sk_B) = (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.96/1.15        | ~ (v1_relat_1 @ sk_B))),
% 0.96/1.15      inference('sup+', [status(thm)], ['115', '116'])).
% 0.96/1.15  thf('118', plain,
% 0.96/1.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('119', plain,
% 0.96/1.15      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.96/1.15         ((v4_relat_1 @ X21 @ X22)
% 0.96/1.15          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.96/1.15      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.96/1.15  thf('120', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.96/1.15      inference('sup-', [status(thm)], ['118', '119'])).
% 0.96/1.15  thf(d18_relat_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( v1_relat_1 @ B ) =>
% 0.96/1.15       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.96/1.15  thf('121', plain,
% 0.96/1.15      (![X13 : $i, X14 : $i]:
% 0.96/1.15         (~ (v4_relat_1 @ X13 @ X14)
% 0.96/1.15          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.96/1.15          | ~ (v1_relat_1 @ X13))),
% 0.96/1.15      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.96/1.15  thf('122', plain,
% 0.96/1.15      ((~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.96/1.15      inference('sup-', [status(thm)], ['120', '121'])).
% 0.96/1.15  thf('123', plain, ((v1_relat_1 @ sk_B)),
% 0.96/1.15      inference('sup-', [status(thm)], ['15', '16'])).
% 0.96/1.15  thf('124', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.96/1.15      inference('demod', [status(thm)], ['122', '123'])).
% 0.96/1.15  thf(t12_xboole_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.96/1.15  thf('125', plain,
% 0.96/1.15      (![X1 : $i, X2 : $i]:
% 0.96/1.15         (((k2_xboole_0 @ X2 @ X1) = (X1)) | ~ (r1_tarski @ X2 @ X1))),
% 0.96/1.15      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.96/1.15  thf('126', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.96/1.15      inference('sup-', [status(thm)], ['124', '125'])).
% 0.96/1.15  thf('127', plain, ((v1_relat_1 @ sk_B)),
% 0.96/1.15      inference('sup-', [status(thm)], ['15', '16'])).
% 0.96/1.15  thf('128', plain, (((k3_relat_1 @ sk_B) = (sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['117', '126', '127'])).
% 0.96/1.15  thf('129', plain, (((k3_relat_1 @ sk_B) = (sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['117', '126', '127'])).
% 0.96/1.15  thf('130', plain,
% 0.96/1.15      ((((k1_xboole_0) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['114', '128', '129'])).
% 0.96/1.15  thf('131', plain, (((sk_A) = (k1_xboole_0))),
% 0.96/1.15      inference('demod', [status(thm)], ['100', '103'])).
% 0.96/1.15  thf('132', plain, (((sk_A) = (k1_xboole_0))),
% 0.96/1.15      inference('demod', [status(thm)], ['100', '103'])).
% 0.96/1.15  thf('133', plain, (((sk_A) = (k1_xboole_0))),
% 0.96/1.15      inference('demod', [status(thm)], ['100', '103'])).
% 0.96/1.15  thf('134', plain,
% 0.96/1.15      ((((k1_xboole_0) != (k1_xboole_0))
% 0.96/1.15        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.96/1.15      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.96/1.15  thf('135', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.96/1.15      inference('simplify', [status(thm)], ['134'])).
% 0.96/1.15  thf(t69_xboole_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.96/1.15       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.96/1.15  thf('136', plain,
% 0.96/1.15      (![X6 : $i, X7 : $i]:
% 0.96/1.15         (~ (r1_xboole_0 @ X6 @ X7)
% 0.96/1.15          | ~ (r1_tarski @ X6 @ X7)
% 0.96/1.15          | (v1_xboole_0 @ X6))),
% 0.96/1.15      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.96/1.15  thf('137', plain,
% 0.96/1.15      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.96/1.15      inference('sup-', [status(thm)], ['135', '136'])).
% 0.96/1.15  thf('138', plain, ((r1_tarski @ (k3_relat_1 @ sk_B) @ sk_A)),
% 0.96/1.15      inference('demod', [status(thm)], ['108', '109'])).
% 0.96/1.15  thf('139', plain, (((k3_relat_1 @ sk_B) = (sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['117', '126', '127'])).
% 0.96/1.15  thf('140', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.96/1.15      inference('demod', [status(thm)], ['138', '139'])).
% 0.96/1.15  thf('141', plain, (((sk_A) = (k1_xboole_0))),
% 0.96/1.15      inference('demod', [status(thm)], ['100', '103'])).
% 0.96/1.15  thf('142', plain, (((sk_A) = (k1_xboole_0))),
% 0.96/1.15      inference('demod', [status(thm)], ['100', '103'])).
% 0.96/1.15  thf('143', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.96/1.15      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.96/1.15  thf('144', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.96/1.15      inference('demod', [status(thm)], ['137', '143'])).
% 0.96/1.15  thf('145', plain, ($false), inference('demod', [status(thm)], ['105', '144'])).
% 0.96/1.15  
% 0.96/1.15  % SZS output end Refutation
% 0.96/1.15  
% 0.96/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
