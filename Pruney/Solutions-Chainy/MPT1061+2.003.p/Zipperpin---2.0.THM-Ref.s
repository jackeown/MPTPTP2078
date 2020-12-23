%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tNqwejgFOR

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 385 expanded)
%              Number of leaves         :   43 ( 127 expanded)
%              Depth                    :   18
%              Number of atoms          : 1294 (8027 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t178_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( v1_xboole_0 @ D )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ A @ D )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
           => ( ( ( r1_tarski @ B @ A )
                & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
             => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
                & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
                & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) )
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
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
        & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( zip_tseitin_0 @ X42 @ X39 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_E @ X0 @ sk_D @ sk_A )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ( zip_tseitin_1 @ sk_D @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_E @ X0 @ sk_D @ sk_A )
      | ( zip_tseitin_1 @ sk_D @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( zip_tseitin_0 @ sk_E @ sk_B @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_funct_2 @ ( k2_partfun1 @ X33 @ X34 @ X35 @ X36 ) @ X36 @ X34 )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k2_partfun1 @ X30 @ X31 @ X29 @ X32 )
        = ( k7_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( zip_tseitin_0 @ sk_E @ sk_B @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ X33 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_D )
    | ( v1_partfun1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X26 @ X27 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_D )
    | ( v1_partfun1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( v1_partfun1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['16','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_partfun1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A )
    | ( v1_partfun1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('37',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k7_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k9_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['37','40'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X43 ) @ X44 )
      | ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X43 ) @ X44 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X26 @ X27 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('59',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('62',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['48','49'])).

thf('68',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('69',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_partfun1 @ X19 @ X20 )
      | ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('70',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( v1_partfun1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('72',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( v1_partfun1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['73'])).

thf('79',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('82',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['73'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['73'])).

thf('86',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['79','84','85'])).

thf('87',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['76','86'])).

thf('88',plain,(
    ~ ( v1_partfun1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['72','87'])).

thf('89',plain,(
    zip_tseitin_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['35','88'])).

thf('90',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('91',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','90'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tNqwejgFOR
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 130 iterations in 0.091s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(t178_funct_2, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.21/0.55       ( ![E:$i]:
% 0.21/0.55         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.21/0.55             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.21/0.55           ( ( ( r1_tarski @ B @ A ) & 
% 0.21/0.55               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.21/0.55             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.21/0.55               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.21/0.55               ( m1_subset_1 @
% 0.21/0.55                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.21/0.55                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55        ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.21/0.55          ( ![E:$i]:
% 0.21/0.55            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.21/0.55                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.21/0.55              ( ( ( r1_tarski @ B @ A ) & 
% 0.21/0.55                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.21/0.55                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.21/0.55                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.21/0.55                  ( m1_subset_1 @
% 0.21/0.55                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.21/0.55                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 0.21/0.55  thf('0', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t38_funct_2, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.55         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.55       ( ( r1_tarski @ C @ A ) =>
% 0.21/0.55         ( ( ( m1_subset_1 @
% 0.21/0.55               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.21/0.55               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.21/0.55             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.21/0.55             ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) ) | 
% 0.21/0.55           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_2, axiom,
% 0.21/0.55    (![B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.21/0.55       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.55  thf(zf_stmt_4, axiom,
% 0.21/0.55    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.55     ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.21/0.55       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 0.21/0.55         ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.21/0.55         ( m1_subset_1 @
% 0.21/0.55           ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.21/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_5, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.55       ( ( r1_tarski @ C @ A ) =>
% 0.21/0.55         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X39 @ X40)
% 0.21/0.55          | (zip_tseitin_1 @ X41 @ X40)
% 0.21/0.55          | ~ (v1_funct_1 @ X42)
% 0.21/0.55          | ~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.21/0.55          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.21/0.55          | (zip_tseitin_0 @ X42 @ X39 @ X41 @ X40))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((zip_tseitin_0 @ sk_E @ X0 @ sk_D @ sk_A)
% 0.21/0.55          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_D)
% 0.21/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.55          | (zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((zip_tseitin_0 @ sk_E @ X0 @ sk_D @ sk_A)
% 0.21/0.55          | (zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (zip_tseitin_0 @ sk_E @ sk_B @ sk_D @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.55         ((v1_funct_2 @ (k2_partfun1 @ X33 @ X34 @ X35 @ X36) @ X36 @ X34)
% 0.21/0.55          | ~ (zip_tseitin_0 @ X35 @ X36 @ X34 @ X33))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.55       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.21/0.55          | ~ (v1_funct_1 @ X29)
% 0.21/0.55          | ((k2_partfun1 @ X30 @ X31 @ X29 @ X32) = (k7_relat_1 @ X29 @ X32)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_D))),
% 0.21/0.55      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (zip_tseitin_0 @ sk_E @ sk_B @ sk_D @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_partfun1 @ X33 @ X34 @ X35 @ X36) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.21/0.55          | ~ (zip_tseitin_0 @ X35 @ X36 @ X34 @ X33))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D))))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf(cc5_funct_2, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.55             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.55          | (v1_partfun1 @ X22 @ X23)
% 0.21/0.55          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.55          | ~ (v1_funct_1 @ X22)
% 0.21/0.55          | (v1_xboole_0 @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_D)
% 0.21/0.55        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.21/0.55        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_D)
% 0.21/0.55        | (v1_partfun1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_k2_partfun1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.55       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.21/0.55         ( m1_subset_1 @
% 0.21/0.55           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.21/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.21/0.55          | ~ (v1_funct_1 @ X25)
% 0.21/0.55          | (v1_funct_1 @ (k2_partfun1 @ X26 @ X27 @ X25 @ X28)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('30', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_D)
% 0.21/0.55        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_D)
% 0.21/0.55        | (v1_partfun1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['23', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (v1_partfun1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B)
% 0.21/0.55        | (v1_xboole_0 @ sk_D)
% 0.21/0.55        | (zip_tseitin_1 @ sk_D @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (((v1_xboole_0 @ sk_D)
% 0.21/0.55        | (v1_partfun1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B)
% 0.21/0.55        | (zip_tseitin_1 @ sk_D @ sk_A))),
% 0.21/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.55  thf('34', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((zip_tseitin_1 @ sk_D @ sk_A)
% 0.21/0.55        | (v1_partfun1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.55  thf(t87_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]:
% 0.21/0.55         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X6 @ X7)) @ X7)
% 0.21/0.55          | ~ (v1_relat_1 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.55          | ((k7_relset_1 @ X12 @ X13 @ X11 @ X14) = (k9_relat_1 @ X11 @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.55  thf('41', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['37', '40'])).
% 0.21/0.55  thf(t148_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.21/0.55          | ~ (v1_relat_1 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.55  thf(t4_funct_2, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.55         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.21/0.55           ( m1_subset_1 @
% 0.21/0.55             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X43 : $i, X44 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X43) @ X44)
% 0.21/0.55          | (m1_subset_1 @ X43 @ 
% 0.21/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X43) @ X44)))
% 0.21/0.55          | ~ (v1_funct_1 @ X43)
% 0.21/0.55          | ~ (v1_relat_1 @ X43))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.21/0.55             (k1_zfmisc_1 @ 
% 0.21/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55         (k1_zfmisc_1 @ 
% 0.21/0.55          (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 0.21/0.55        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.21/0.55        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_E))),
% 0.21/0.55      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.55          | (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 0.21/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf(fc6_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.55  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55         (k1_zfmisc_1 @ 
% 0.21/0.55          (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 0.21/0.55        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.21/0.55        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '50'])).
% 0.21/0.55  thf('52', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55         (k1_zfmisc_1 @ 
% 0.21/0.55          (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 0.21/0.55        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.21/0.55          | ~ (v1_funct_1 @ X25)
% 0.21/0.55          | (m1_subset_1 @ (k2_partfun1 @ X26 @ X27 @ X25 @ X28) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 0.21/0.55          | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 0.21/0.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.21/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.55  thf(cc1_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( v1_relat_1 @ C ) ))).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.55         ((v1_relat_1 @ X8)
% 0.21/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X0 : $i]: (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('62', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['53', '62'])).
% 0.21/0.55  thf(t13_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.55       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.21/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.21/0.55          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.21/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.21/0.55      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))
% 0.21/0.55          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_E)
% 0.21/0.55        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['36', '65'])).
% 0.21/0.55  thf('67', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf(cc1_funct_2, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.21/0.55         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (v1_funct_1 @ X19)
% 0.21/0.55          | ~ (v1_partfun1 @ X19 @ X20)
% 0.21/0.55          | (v1_funct_2 @ X19 @ X20 @ X21)
% 0.21/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.21/0.55        | ~ (v1_partfun1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B)
% 0.21/0.55        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.55  thf('71', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.21/0.55        | ~ (v1_partfun1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 0.21/0.55        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.21/0.55             sk_C)
% 0.21/0.55        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.21/0.55               sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['73'])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.21/0.55               sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))
% 0.21/0.55         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['73'])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.21/0.55      inference('split', [status(esa)], ['73'])).
% 0.21/0.55  thf('83', plain,
% 0.21/0.55      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.21/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['80', '83'])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (~
% 0.21/0.55       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C)) | 
% 0.21/0.55       ~
% 0.21/0.55       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.21/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))) | 
% 0.21/0.55       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.21/0.55      inference('split', [status(esa)], ['73'])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      (~
% 0.21/0.55       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['79', '84', '85'])).
% 0.21/0.55  thf('87', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['76', '86'])).
% 0.21/0.55  thf('88', plain, (~ (v1_partfun1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B)),
% 0.21/0.55      inference('clc', [status(thm)], ['72', '87'])).
% 0.21/0.55  thf('89', plain, ((zip_tseitin_1 @ sk_D @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['35', '88'])).
% 0.21/0.55  thf('90', plain,
% 0.21/0.55      (![X37 : $i, X38 : $i]:
% 0.21/0.55         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.55  thf('91', plain, (((sk_D) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.55  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('93', plain, ($false),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '91', '92'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
