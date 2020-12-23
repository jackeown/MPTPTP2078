%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G3tJuZeAhK

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:25 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 455 expanded)
%              Number of leaves         :   43 ( 151 expanded)
%              Depth                    :   20
%              Number of atoms          : 1282 (8078 expanded)
%              Number of equality atoms :   64 ( 126 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('16',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('21',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X46 @ X44 @ X44 @ X45 @ X47 @ X43 ) )
      | ( v2_funct_1 @ X47 )
      | ( X45 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X44 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('28',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29','30','31','32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('45',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('50',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('51',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('65',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('70',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['49','52','63','64','65','70','71'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('74',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('76',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','76'])).

thf('78',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('79',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('80',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('83',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['2','78','83'])).

thf('85',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('88',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('89',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('90',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('94',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('99',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['68','69'])).

thf('102',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('104',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['68','69'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['92','95','102','103','104','105','106'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('108',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ X29 )
       != X28 )
      | ( v2_funct_2 @ X29 @ X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('109',plain,(
    ! [X29: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
      | ( v2_funct_2 @ X29 @ ( k2_relat_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X29: $i] :
      ( ( v2_funct_2 @ X29 @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(clc,[status(thm)],['109','113'])).

thf('115',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['68','69'])).

thf('117',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['87','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G3tJuZeAhK
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 413 iterations in 0.161s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.43/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.61  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.43/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.43/0.61  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.43/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.43/0.61  thf(t29_funct_2, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.61       ( ![D:$i]:
% 0.43/0.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.43/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.43/0.61           ( ( r2_relset_1 @
% 0.43/0.61               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.43/0.61               ( k6_partfun1 @ A ) ) =>
% 0.43/0.61             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.61          ( ![D:$i]:
% 0.43/0.61            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.43/0.61                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.43/0.61              ( ( r2_relset_1 @
% 0.43/0.61                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.43/0.61                  ( k6_partfun1 @ A ) ) =>
% 0.43/0.61                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.43/0.61  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('2', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.61        (k6_partfun1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(dt_k1_partfun1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.43/0.61     ( ( ( v1_funct_1 @ E ) & 
% 0.43/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.43/0.61         ( v1_funct_1 @ F ) & 
% 0.43/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.43/0.61       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.43/0.61         ( m1_subset_1 @
% 0.43/0.61           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.43/0.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.43/0.61          | ~ (v1_funct_1 @ X30)
% 0.43/0.61          | ~ (v1_funct_1 @ X33)
% 0.43/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.43/0.61          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 0.43/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.43/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.43/0.61          | ~ (v1_funct_1 @ X1)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.61  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.43/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.43/0.61          | ~ (v1_funct_1 @ X1))),
% 0.43/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      ((~ (v1_funct_1 @ sk_D)
% 0.43/0.61        | (m1_subset_1 @ 
% 0.43/0.61           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '9'])).
% 0.43/0.61  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      ((m1_subset_1 @ 
% 0.43/0.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf(redefinition_r2_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.43/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.61       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.43/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.43/0.61          | ((X23) = (X26))
% 0.43/0.61          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.61             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.43/0.61          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.43/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.43/0.61        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.43/0.61            = (k6_partfun1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['3', '14'])).
% 0.43/0.61  thf(t29_relset_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( m1_subset_1 @
% 0.43/0.61       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      (![X27 : $i]:
% 0.43/0.61         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.43/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.43/0.61  thf(redefinition_k6_partfun1, axiom,
% 0.43/0.61    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.43/0.61  thf('17', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X27 : $i]:
% 0.43/0.61         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.43/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.43/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.43/0.61         = (k6_partfun1 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['15', '18'])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t26_funct_2, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.43/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.61       ( ![E:$i]:
% 0.43/0.61         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.43/0.61             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.43/0.61           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.43/0.61             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.43/0.61               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.43/0.61         (~ (v1_funct_1 @ X43)
% 0.43/0.61          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.43/0.61          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.43/0.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X46 @ X44 @ X44 @ X45 @ X47 @ X43))
% 0.43/0.61          | (v2_funct_1 @ X47)
% 0.43/0.61          | ((X45) = (k1_xboole_0))
% 0.43/0.61          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.43/0.61          | ~ (v1_funct_2 @ X47 @ X46 @ X44)
% 0.43/0.61          | ~ (v1_funct_1 @ X47))),
% 0.43/0.61      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.43/0.61          | ((sk_A) = (k1_xboole_0))
% 0.43/0.61          | (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.43/0.61          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_D))),
% 0.43/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.61  thf('23', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.43/0.61          | ((sk_A) = (k1_xboole_0))
% 0.43/0.61          | (v2_funct_1 @ X0)
% 0.43/0.61          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.43/0.61      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.43/0.61        | (v2_funct_1 @ sk_C)
% 0.43/0.61        | ((sk_A) = (k1_xboole_0))
% 0.43/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.43/0.61        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.43/0.61        | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.43/0.61  thf(fc4_funct_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.43/0.61       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.43/0.61  thf('27', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.43/0.61  thf('28', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.61  thf('29', plain, (![X19 : $i]: (v2_funct_1 @ (k6_partfun1 @ X19))),
% 0.43/0.61      inference('demod', [status(thm)], ['27', '28'])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('33', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['26', '29', '30', '31', '32'])).
% 0.43/0.61  thf('34', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('35', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(redefinition_k1_partfun1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.43/0.61     ( ( ( v1_funct_1 @ E ) & 
% 0.43/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.43/0.61         ( v1_funct_1 @ F ) & 
% 0.43/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.43/0.61       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.43/0.61          | ~ (v1_funct_1 @ X36)
% 0.43/0.61          | ~ (v1_funct_1 @ X39)
% 0.43/0.61          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.43/0.61          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.43/0.61              = (k5_relat_1 @ X36 @ X39)))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.43/0.61            = (k5_relat_1 @ sk_C @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.43/0.61            = (k5_relat_1 @ sk_C @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.43/0.61          | ~ (v1_funct_1 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      ((~ (v1_funct_1 @ sk_D)
% 0.43/0.61        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.43/0.61            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['36', '41'])).
% 0.43/0.61  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.43/0.61         = (k6_partfun1 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['15', '18'])).
% 0.43/0.61  thf('45', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.43/0.61      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.43/0.61  thf(t44_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( v1_relat_1 @ B ) =>
% 0.43/0.61           ( r1_tarski @
% 0.43/0.61             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X11)
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 0.43/0.61             (k1_relat_1 @ X12))
% 0.43/0.61          | ~ (v1_relat_1 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.43/0.61  thf(d10_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i]:
% 0.43/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ X1)
% 0.43/0.61          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.43/0.61               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.43/0.61          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.43/0.61           (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 0.43/0.61        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_D)
% 0.43/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['45', '48'])).
% 0.43/0.61  thf(t71_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.43/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.43/0.61  thf('50', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.61  thf('51', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.61  thf('52', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 0.43/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc2_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.61         ((v4_relat_1 @ X20 @ X21)
% 0.43/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.61  thf('55', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.43/0.61  thf(d18_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (![X5 : $i, X6 : $i]:
% 0.43/0.61         (~ (v4_relat_1 @ X5 @ X6)
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.43/0.61          | ~ (v1_relat_1 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc2_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.43/0.61          | (v1_relat_1 @ X3)
% 0.43/0.61          | ~ (v1_relat_1 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.43/0.61  thf(fc6_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.43/0.61  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('demod', [status(thm)], ['60', '61'])).
% 0.43/0.61  thf('63', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['57', '62'])).
% 0.43/0.61  thf('64', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.43/0.61      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.43/0.61  thf('65', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 0.43/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('67', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.43/0.61          | (v1_relat_1 @ X3)
% 0.43/0.61          | ~ (v1_relat_1 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.43/0.61  thf('68', plain,
% 0.43/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.43/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.43/0.61  thf('69', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.43/0.61  thf('70', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69'])).
% 0.43/0.61  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('demod', [status(thm)], ['60', '61'])).
% 0.43/0.61  thf('72', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['49', '52', '63', '64', '65', '70', '71'])).
% 0.43/0.61  thf(t64_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.61           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.61         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.61  thf('73', plain,
% 0.43/0.61      (![X15 : $i]:
% 0.43/0.61         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 0.43/0.61          | ((X15) = (k1_xboole_0))
% 0.43/0.61          | ~ (v1_relat_1 @ X15))),
% 0.43/0.61      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.43/0.61  thf('74', plain,
% 0.43/0.61      ((((sk_A) != (k1_xboole_0))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.43/0.61        | ((sk_C) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.43/0.61  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('demod', [status(thm)], ['60', '61'])).
% 0.43/0.61  thf('76', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['74', '75'])).
% 0.43/0.61  thf('77', plain,
% 0.43/0.61      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0))))
% 0.43/0.61         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['35', '76'])).
% 0.43/0.61  thf('78', plain, ((((sk_C) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['77'])).
% 0.43/0.61  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.43/0.61  thf('79', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.43/0.61  thf('80', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.61  thf('81', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.43/0.61  thf('82', plain, (![X19 : $i]: (v2_funct_1 @ (k6_partfun1 @ X19))),
% 0.43/0.61      inference('demod', [status(thm)], ['27', '28'])).
% 0.43/0.61  thf('83', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['81', '82'])).
% 0.43/0.61  thf('84', plain, (((v2_funct_1 @ sk_C))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '78', '83'])).
% 0.43/0.61  thf('85', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('86', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.43/0.61  thf('87', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 0.43/0.61  thf('88', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.43/0.61      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.43/0.61  thf(t45_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( v1_relat_1 @ B ) =>
% 0.43/0.61           ( r1_tarski @
% 0.43/0.61             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X13)
% 0.43/0.61          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 0.43/0.61             (k2_relat_1 @ X13))
% 0.43/0.61          | ~ (v1_relat_1 @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i]:
% 0.43/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('91', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X1)
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.43/0.61               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.43/0.61          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['89', '90'])).
% 0.43/0.61  thf('92', plain,
% 0.43/0.61      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.43/0.61           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 0.43/0.61        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_D)
% 0.43/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['88', '91'])).
% 0.43/0.61  thf('93', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.61  thf('94', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.61  thf('95', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.43/0.61      inference('demod', [status(thm)], ['93', '94'])).
% 0.43/0.61  thf('96', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('97', plain,
% 0.43/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.61         ((v5_relat_1 @ X20 @ X22)
% 0.43/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.61  thf('98', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['96', '97'])).
% 0.43/0.61  thf(d19_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.43/0.61  thf('99', plain,
% 0.43/0.61      (![X7 : $i, X8 : $i]:
% 0.43/0.61         (~ (v5_relat_1 @ X7 @ X8)
% 0.43/0.61          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.43/0.61          | ~ (v1_relat_1 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.43/0.61  thf('100', plain,
% 0.43/0.61      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['98', '99'])).
% 0.43/0.61  thf('101', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69'])).
% 0.43/0.61  thf('102', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['100', '101'])).
% 0.43/0.61  thf('103', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.43/0.61      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.43/0.61  thf('104', plain,
% 0.43/0.61      (![X17 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.43/0.61      inference('demod', [status(thm)], ['93', '94'])).
% 0.43/0.61  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69'])).
% 0.43/0.61  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.61      inference('demod', [status(thm)], ['60', '61'])).
% 0.43/0.61  thf('107', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['92', '95', '102', '103', '104', '105', '106'])).
% 0.43/0.61  thf(d3_funct_2, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.43/0.61       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.43/0.61  thf('108', plain,
% 0.43/0.61      (![X28 : $i, X29 : $i]:
% 0.43/0.61         (((k2_relat_1 @ X29) != (X28))
% 0.43/0.61          | (v2_funct_2 @ X29 @ X28)
% 0.43/0.61          | ~ (v5_relat_1 @ X29 @ X28)
% 0.43/0.61          | ~ (v1_relat_1 @ X29))),
% 0.43/0.61      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.43/0.61  thf('109', plain,
% 0.43/0.61      (![X29 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X29)
% 0.43/0.61          | ~ (v5_relat_1 @ X29 @ (k2_relat_1 @ X29))
% 0.43/0.61          | (v2_funct_2 @ X29 @ (k2_relat_1 @ X29)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['108'])).
% 0.43/0.61  thf('110', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('111', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.43/0.61      inference('simplify', [status(thm)], ['110'])).
% 0.43/0.61  thf('112', plain,
% 0.43/0.61      (![X7 : $i, X8 : $i]:
% 0.43/0.61         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.43/0.61          | (v5_relat_1 @ X7 @ X8)
% 0.43/0.61          | ~ (v1_relat_1 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.43/0.61  thf('113', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['111', '112'])).
% 0.43/0.61  thf('114', plain,
% 0.43/0.61      (![X29 : $i]:
% 0.43/0.61         ((v2_funct_2 @ X29 @ (k2_relat_1 @ X29)) | ~ (v1_relat_1 @ X29))),
% 0.43/0.61      inference('clc', [status(thm)], ['109', '113'])).
% 0.43/0.61  thf('115', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 0.43/0.61      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.61  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.61      inference('demod', [status(thm)], ['68', '69'])).
% 0.43/0.61  thf('117', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['115', '116'])).
% 0.43/0.61  thf('118', plain, ($false), inference('demod', [status(thm)], ['87', '117'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
