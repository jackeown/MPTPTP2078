%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OzXmXUc477

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:19 EST 2020

% Result     : Theorem 4.56s
% Output     : Refutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 302 expanded)
%              Number of leaves         :   46 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          : 1188 (5144 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('3',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ( X5 = X6 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['14'])).

thf('16',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49 ) )
      | ( v2_funct_1 @ X53 )
      | ( X51 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X50 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','52'])).

thf('54',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('66',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('71',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('72',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('73',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('75',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('76',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('77',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('82',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('86',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['81','82'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['70','73','84','85','86','87','92'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('94',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('95',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X33: $i] :
      ( ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(clc,[status(thm)],['95','99'])).

thf('101',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['93','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['81','82'])).

thf('103',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['56','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OzXmXUc477
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:15:34 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 4.56/4.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.56/4.75  % Solved by: fo/fo7.sh
% 4.56/4.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.56/4.75  % done 3899 iterations in 4.307s
% 4.56/4.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.56/4.75  % SZS output start Refutation
% 4.56/4.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.56/4.75  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.56/4.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.56/4.75  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.56/4.75  thf(sk_D_type, type, sk_D: $i).
% 4.56/4.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.56/4.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.56/4.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.56/4.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.56/4.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.56/4.75  thf(sk_A_type, type, sk_A: $i).
% 4.56/4.75  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.56/4.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.56/4.75  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.56/4.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.56/4.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.56/4.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.56/4.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.56/4.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.56/4.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.56/4.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.56/4.75  thf(sk_C_type, type, sk_C: $i).
% 4.56/4.75  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.56/4.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.56/4.75  thf(sk_B_type, type, sk_B: $i).
% 4.56/4.75  thf(t29_funct_2, conjecture,
% 4.56/4.75    (![A:$i,B:$i,C:$i]:
% 4.56/4.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.56/4.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.56/4.75       ( ![D:$i]:
% 4.56/4.75         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.56/4.75             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.56/4.75           ( ( r2_relset_1 @
% 4.56/4.75               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.56/4.75               ( k6_partfun1 @ A ) ) =>
% 4.56/4.75             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.56/4.75  thf(zf_stmt_0, negated_conjecture,
% 4.56/4.75    (~( ![A:$i,B:$i,C:$i]:
% 4.56/4.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.56/4.75            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.56/4.75          ( ![D:$i]:
% 4.56/4.75            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.56/4.75                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.56/4.75              ( ( r2_relset_1 @
% 4.56/4.75                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.56/4.75                  ( k6_partfun1 @ A ) ) =>
% 4.56/4.75                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.56/4.75    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.56/4.75  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('1', plain,
% 4.56/4.75      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.56/4.75      inference('split', [status(esa)], ['0'])).
% 4.56/4.75  thf(fc3_zfmisc_1, axiom,
% 4.56/4.75    (![A:$i,B:$i]:
% 4.56/4.75     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.56/4.75  thf('2', plain,
% 4.56/4.75      (![X7 : $i, X8 : $i]:
% 4.56/4.75         ((v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 4.56/4.75      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 4.56/4.75  thf(dt_k6_partfun1, axiom,
% 4.56/4.75    (![A:$i]:
% 4.56/4.75     ( ( m1_subset_1 @
% 4.56/4.75         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.56/4.75       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.56/4.75  thf('3', plain,
% 4.56/4.75      (![X41 : $i]:
% 4.56/4.75         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 4.56/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 4.56/4.75      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.56/4.75  thf(cc1_subset_1, axiom,
% 4.56/4.75    (![A:$i]:
% 4.56/4.75     ( ( v1_xboole_0 @ A ) =>
% 4.56/4.75       ( ![B:$i]:
% 4.56/4.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 4.56/4.75  thf('4', plain,
% 4.56/4.75      (![X11 : $i, X12 : $i]:
% 4.56/4.75         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 4.56/4.75          | (v1_xboole_0 @ X11)
% 4.56/4.75          | ~ (v1_xboole_0 @ X12))),
% 4.56/4.75      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.56/4.75  thf('5', plain,
% 4.56/4.75      (![X0 : $i]:
% 4.56/4.75         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 4.56/4.75          | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 4.56/4.75      inference('sup-', [status(thm)], ['3', '4'])).
% 4.56/4.75  thf('6', plain,
% 4.56/4.75      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 4.56/4.75      inference('sup-', [status(thm)], ['2', '5'])).
% 4.56/4.75  thf(t8_boole, axiom,
% 4.56/4.75    (![A:$i,B:$i]:
% 4.56/4.75     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.56/4.75  thf('7', plain,
% 4.56/4.75      (![X5 : $i, X6 : $i]:
% 4.56/4.75         (~ (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X6) | ((X5) = (X6)))),
% 4.56/4.75      inference('cnf', [status(esa)], [t8_boole])).
% 4.56/4.75  thf('8', plain,
% 4.56/4.75      (![X0 : $i, X1 : $i]:
% 4.56/4.75         (~ (v1_xboole_0 @ X0)
% 4.56/4.75          | ((k6_partfun1 @ X0) = (X1))
% 4.56/4.75          | ~ (v1_xboole_0 @ X1))),
% 4.56/4.75      inference('sup-', [status(thm)], ['6', '7'])).
% 4.56/4.75  thf('9', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.56/4.75      inference('split', [status(esa)], ['0'])).
% 4.56/4.75  thf('10', plain,
% 4.56/4.75      ((![X0 : $i]:
% 4.56/4.75          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 4.56/4.75           | ~ (v1_xboole_0 @ sk_C)
% 4.56/4.75           | ~ (v1_xboole_0 @ X0)))
% 4.56/4.75         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.56/4.75      inference('sup-', [status(thm)], ['8', '9'])).
% 4.56/4.75  thf(fc4_funct_1, axiom,
% 4.56/4.75    (![A:$i]:
% 4.56/4.75     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.56/4.75       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.56/4.75  thf('11', plain, (![X24 : $i]: (v2_funct_1 @ (k6_relat_1 @ X24))),
% 4.56/4.75      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.56/4.75  thf(redefinition_k6_partfun1, axiom,
% 4.56/4.75    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.56/4.75  thf('12', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 4.56/4.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.56/4.75  thf('13', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 4.56/4.75      inference('demod', [status(thm)], ['11', '12'])).
% 4.56/4.75  thf('14', plain,
% 4.56/4.75      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 4.56/4.75         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.56/4.75      inference('demod', [status(thm)], ['10', '13'])).
% 4.56/4.75  thf('15', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.56/4.75      inference('condensation', [status(thm)], ['14'])).
% 4.56/4.75  thf('16', plain,
% 4.56/4.75      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.56/4.75        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.56/4.75        (k6_partfun1 @ sk_A))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('17', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('18', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf(dt_k1_partfun1, axiom,
% 4.56/4.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.56/4.75     ( ( ( v1_funct_1 @ E ) & 
% 4.56/4.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.56/4.75         ( v1_funct_1 @ F ) & 
% 4.56/4.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.56/4.75       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.56/4.75         ( m1_subset_1 @
% 4.56/4.75           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.56/4.75           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.56/4.75  thf('19', plain,
% 4.56/4.75      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 4.56/4.75         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.56/4.75          | ~ (v1_funct_1 @ X34)
% 4.56/4.75          | ~ (v1_funct_1 @ X37)
% 4.56/4.75          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 4.56/4.75          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 4.56/4.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 4.56/4.75      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.56/4.75  thf('20', plain,
% 4.56/4.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.75         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.56/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.56/4.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.56/4.75          | ~ (v1_funct_1 @ X1)
% 4.56/4.75          | ~ (v1_funct_1 @ sk_C))),
% 4.56/4.75      inference('sup-', [status(thm)], ['18', '19'])).
% 4.56/4.75  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('22', plain,
% 4.56/4.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.75         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.56/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.56/4.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.56/4.75          | ~ (v1_funct_1 @ X1))),
% 4.56/4.75      inference('demod', [status(thm)], ['20', '21'])).
% 4.56/4.75  thf('23', plain,
% 4.56/4.75      ((~ (v1_funct_1 @ sk_D)
% 4.56/4.75        | (m1_subset_1 @ 
% 4.56/4.75           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.56/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.56/4.75      inference('sup-', [status(thm)], ['17', '22'])).
% 4.56/4.75  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('25', plain,
% 4.56/4.75      ((m1_subset_1 @ 
% 4.56/4.75        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.56/4.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.56/4.75      inference('demod', [status(thm)], ['23', '24'])).
% 4.56/4.75  thf(redefinition_r2_relset_1, axiom,
% 4.56/4.75    (![A:$i,B:$i,C:$i,D:$i]:
% 4.56/4.75     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.56/4.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.56/4.75       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.56/4.75  thf('26', plain,
% 4.56/4.75      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.56/4.75         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.56/4.75          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.56/4.75          | ((X28) = (X31))
% 4.56/4.75          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 4.56/4.75      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.56/4.75  thf('27', plain,
% 4.56/4.75      (![X0 : $i]:
% 4.56/4.75         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.56/4.75             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 4.56/4.75          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 4.56/4.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.56/4.75      inference('sup-', [status(thm)], ['25', '26'])).
% 4.56/4.75  thf('28', plain,
% 4.56/4.75      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.56/4.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.56/4.75        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.56/4.75            = (k6_partfun1 @ sk_A)))),
% 4.56/4.75      inference('sup-', [status(thm)], ['16', '27'])).
% 4.56/4.75  thf('29', plain,
% 4.56/4.75      (![X41 : $i]:
% 4.56/4.75         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 4.56/4.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 4.56/4.75      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.56/4.75  thf('30', plain,
% 4.56/4.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.56/4.75         = (k6_partfun1 @ sk_A))),
% 4.56/4.75      inference('demod', [status(thm)], ['28', '29'])).
% 4.56/4.75  thf('31', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf(t26_funct_2, axiom,
% 4.56/4.75    (![A:$i,B:$i,C:$i,D:$i]:
% 4.56/4.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.56/4.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.56/4.75       ( ![E:$i]:
% 4.56/4.75         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.56/4.75             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.56/4.75           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.56/4.75             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.56/4.75               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.56/4.75  thf('32', plain,
% 4.56/4.75      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 4.56/4.75         (~ (v1_funct_1 @ X49)
% 4.56/4.75          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 4.56/4.75          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 4.56/4.75          | ~ (v2_funct_1 @ (k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49))
% 4.56/4.75          | (v2_funct_1 @ X53)
% 4.56/4.75          | ((X51) = (k1_xboole_0))
% 4.56/4.75          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 4.56/4.75          | ~ (v1_funct_2 @ X53 @ X52 @ X50)
% 4.56/4.75          | ~ (v1_funct_1 @ X53))),
% 4.56/4.75      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.56/4.75  thf('33', plain,
% 4.56/4.75      (![X0 : $i, X1 : $i]:
% 4.56/4.75         (~ (v1_funct_1 @ X0)
% 4.56/4.75          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.56/4.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.56/4.75          | ((sk_A) = (k1_xboole_0))
% 4.56/4.75          | (v2_funct_1 @ X0)
% 4.56/4.75          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.56/4.75          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.56/4.75          | ~ (v1_funct_1 @ sk_D))),
% 4.56/4.75      inference('sup-', [status(thm)], ['31', '32'])).
% 4.56/4.75  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('36', plain,
% 4.56/4.75      (![X0 : $i, X1 : $i]:
% 4.56/4.75         (~ (v1_funct_1 @ X0)
% 4.56/4.75          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.56/4.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.56/4.75          | ((sk_A) = (k1_xboole_0))
% 4.56/4.75          | (v2_funct_1 @ X0)
% 4.56/4.75          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.56/4.75      inference('demod', [status(thm)], ['33', '34', '35'])).
% 4.56/4.75  thf('37', plain,
% 4.56/4.75      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 4.56/4.75        | (v2_funct_1 @ sk_C)
% 4.56/4.75        | ((sk_A) = (k1_xboole_0))
% 4.56/4.75        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.56/4.75        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.56/4.75        | ~ (v1_funct_1 @ sk_C))),
% 4.56/4.75      inference('sup-', [status(thm)], ['30', '36'])).
% 4.56/4.75  thf('38', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 4.56/4.75      inference('demod', [status(thm)], ['11', '12'])).
% 4.56/4.75  thf('39', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('40', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('42', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.56/4.75      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 4.56/4.75  thf('43', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.56/4.75      inference('split', [status(esa)], ['0'])).
% 4.56/4.75  thf('44', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.56/4.75      inference('sup-', [status(thm)], ['42', '43'])).
% 4.56/4.75  thf(fc4_zfmisc_1, axiom,
% 4.56/4.75    (![A:$i,B:$i]:
% 4.56/4.75     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.56/4.75  thf('45', plain,
% 4.56/4.75      (![X9 : $i, X10 : $i]:
% 4.56/4.75         (~ (v1_xboole_0 @ X9) | (v1_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 4.56/4.75      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.56/4.75  thf('46', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('47', plain,
% 4.56/4.75      (![X11 : $i, X12 : $i]:
% 4.56/4.75         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 4.56/4.75          | (v1_xboole_0 @ X11)
% 4.56/4.75          | ~ (v1_xboole_0 @ X12))),
% 4.56/4.75      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.56/4.75  thf('48', plain,
% 4.56/4.75      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 4.56/4.75      inference('sup-', [status(thm)], ['46', '47'])).
% 4.56/4.75  thf('49', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 4.56/4.75      inference('sup-', [status(thm)], ['45', '48'])).
% 4.56/4.75  thf('50', plain,
% 4.56/4.75      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 4.56/4.75         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.56/4.75      inference('sup-', [status(thm)], ['44', '49'])).
% 4.56/4.75  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.56/4.75  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.56/4.75      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.56/4.75  thf('52', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.56/4.75      inference('demod', [status(thm)], ['50', '51'])).
% 4.56/4.75  thf('53', plain, (((v2_funct_1 @ sk_C))),
% 4.56/4.75      inference('demod', [status(thm)], ['15', '52'])).
% 4.56/4.75  thf('54', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 4.56/4.75      inference('split', [status(esa)], ['0'])).
% 4.56/4.75  thf('55', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.56/4.75      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 4.56/4.75  thf('56', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 4.56/4.75      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 4.56/4.75  thf('57', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('58', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf(redefinition_k1_partfun1, axiom,
% 4.56/4.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.56/4.75     ( ( ( v1_funct_1 @ E ) & 
% 4.56/4.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.56/4.75         ( v1_funct_1 @ F ) & 
% 4.56/4.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.56/4.75       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.56/4.75  thf('59', plain,
% 4.56/4.75      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 4.56/4.75         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 4.56/4.75          | ~ (v1_funct_1 @ X42)
% 4.56/4.75          | ~ (v1_funct_1 @ X45)
% 4.56/4.75          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 4.56/4.75          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 4.56/4.75              = (k5_relat_1 @ X42 @ X45)))),
% 4.56/4.75      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.56/4.75  thf('60', plain,
% 4.56/4.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.56/4.75            = (k5_relat_1 @ sk_C @ X0))
% 4.56/4.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.56/4.75          | ~ (v1_funct_1 @ X0)
% 4.56/4.75          | ~ (v1_funct_1 @ sk_C))),
% 4.56/4.75      inference('sup-', [status(thm)], ['58', '59'])).
% 4.56/4.75  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('62', plain,
% 4.56/4.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.56/4.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.56/4.75            = (k5_relat_1 @ sk_C @ X0))
% 4.56/4.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.56/4.75          | ~ (v1_funct_1 @ X0))),
% 4.56/4.75      inference('demod', [status(thm)], ['60', '61'])).
% 4.56/4.75  thf('63', plain,
% 4.56/4.75      ((~ (v1_funct_1 @ sk_D)
% 4.56/4.75        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.56/4.75            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.56/4.75      inference('sup-', [status(thm)], ['57', '62'])).
% 4.56/4.75  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('65', plain,
% 4.56/4.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.56/4.75         = (k6_partfun1 @ sk_A))),
% 4.56/4.75      inference('demod', [status(thm)], ['28', '29'])).
% 4.56/4.75  thf('66', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 4.56/4.75      inference('demod', [status(thm)], ['63', '64', '65'])).
% 4.56/4.75  thf(t45_relat_1, axiom,
% 4.56/4.75    (![A:$i]:
% 4.56/4.75     ( ( v1_relat_1 @ A ) =>
% 4.56/4.75       ( ![B:$i]:
% 4.56/4.75         ( ( v1_relat_1 @ B ) =>
% 4.56/4.75           ( r1_tarski @
% 4.56/4.75             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 4.56/4.75  thf('67', plain,
% 4.56/4.75      (![X19 : $i, X20 : $i]:
% 4.56/4.75         (~ (v1_relat_1 @ X19)
% 4.56/4.75          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 4.56/4.75             (k2_relat_1 @ X19))
% 4.56/4.75          | ~ (v1_relat_1 @ X20))),
% 4.56/4.75      inference('cnf', [status(esa)], [t45_relat_1])).
% 4.56/4.75  thf(d10_xboole_0, axiom,
% 4.56/4.75    (![A:$i,B:$i]:
% 4.56/4.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.56/4.75  thf('68', plain,
% 4.56/4.75      (![X1 : $i, X3 : $i]:
% 4.56/4.75         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 4.56/4.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.56/4.75  thf('69', plain,
% 4.56/4.75      (![X0 : $i, X1 : $i]:
% 4.56/4.75         (~ (v1_relat_1 @ X1)
% 4.56/4.75          | ~ (v1_relat_1 @ X0)
% 4.56/4.75          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 4.56/4.75               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 4.56/4.75          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 4.56/4.75      inference('sup-', [status(thm)], ['67', '68'])).
% 4.56/4.75  thf('70', plain,
% 4.56/4.75      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 4.56/4.75           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 4.56/4.75        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 4.56/4.75        | ~ (v1_relat_1 @ sk_D)
% 4.56/4.75        | ~ (v1_relat_1 @ sk_C))),
% 4.56/4.75      inference('sup-', [status(thm)], ['66', '69'])).
% 4.56/4.75  thf(t71_relat_1, axiom,
% 4.56/4.75    (![A:$i]:
% 4.56/4.75     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.56/4.75       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.56/4.75  thf('71', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 4.56/4.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.56/4.75  thf('72', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 4.56/4.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.56/4.75  thf('73', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 4.56/4.75      inference('demod', [status(thm)], ['71', '72'])).
% 4.56/4.75  thf('74', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf(cc2_relset_1, axiom,
% 4.56/4.75    (![A:$i,B:$i,C:$i]:
% 4.56/4.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.56/4.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.56/4.75  thf('75', plain,
% 4.56/4.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.56/4.75         ((v5_relat_1 @ X25 @ X27)
% 4.56/4.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.56/4.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.56/4.75  thf('76', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.56/4.75      inference('sup-', [status(thm)], ['74', '75'])).
% 4.56/4.75  thf(d19_relat_1, axiom,
% 4.56/4.75    (![A:$i,B:$i]:
% 4.56/4.75     ( ( v1_relat_1 @ B ) =>
% 4.56/4.75       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.56/4.75  thf('77', plain,
% 4.56/4.75      (![X15 : $i, X16 : $i]:
% 4.56/4.75         (~ (v5_relat_1 @ X15 @ X16)
% 4.56/4.75          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.56/4.75          | ~ (v1_relat_1 @ X15))),
% 4.56/4.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.56/4.75  thf('78', plain,
% 4.56/4.75      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 4.56/4.75      inference('sup-', [status(thm)], ['76', '77'])).
% 4.56/4.75  thf('79', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf(cc2_relat_1, axiom,
% 4.56/4.75    (![A:$i]:
% 4.56/4.75     ( ( v1_relat_1 @ A ) =>
% 4.56/4.75       ( ![B:$i]:
% 4.56/4.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.56/4.75  thf('80', plain,
% 4.56/4.75      (![X13 : $i, X14 : $i]:
% 4.56/4.75         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.56/4.75          | (v1_relat_1 @ X13)
% 4.56/4.75          | ~ (v1_relat_1 @ X14))),
% 4.56/4.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.56/4.75  thf('81', plain,
% 4.56/4.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.56/4.75      inference('sup-', [status(thm)], ['79', '80'])).
% 4.56/4.75  thf(fc6_relat_1, axiom,
% 4.56/4.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.56/4.75  thf('82', plain,
% 4.56/4.75      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 4.56/4.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.56/4.75  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 4.56/4.75      inference('demod', [status(thm)], ['81', '82'])).
% 4.56/4.75  thf('84', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 4.56/4.75      inference('demod', [status(thm)], ['78', '83'])).
% 4.56/4.75  thf('85', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 4.56/4.75      inference('demod', [status(thm)], ['63', '64', '65'])).
% 4.56/4.75  thf('86', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 4.56/4.75      inference('demod', [status(thm)], ['71', '72'])).
% 4.56/4.75  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 4.56/4.75      inference('demod', [status(thm)], ['81', '82'])).
% 4.56/4.75  thf('88', plain,
% 4.56/4.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.56/4.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.56/4.75  thf('89', plain,
% 4.56/4.75      (![X13 : $i, X14 : $i]:
% 4.56/4.75         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.56/4.75          | (v1_relat_1 @ X13)
% 4.56/4.75          | ~ (v1_relat_1 @ X14))),
% 4.56/4.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.56/4.75  thf('90', plain,
% 4.56/4.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.56/4.75      inference('sup-', [status(thm)], ['88', '89'])).
% 4.56/4.75  thf('91', plain,
% 4.56/4.75      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 4.56/4.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.56/4.75  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 4.56/4.75      inference('demod', [status(thm)], ['90', '91'])).
% 4.56/4.75  thf('93', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.56/4.75      inference('demod', [status(thm)],
% 4.56/4.75                ['70', '73', '84', '85', '86', '87', '92'])).
% 4.56/4.75  thf(d3_funct_2, axiom,
% 4.56/4.75    (![A:$i,B:$i]:
% 4.56/4.75     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.56/4.75       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.56/4.75  thf('94', plain,
% 4.56/4.75      (![X32 : $i, X33 : $i]:
% 4.56/4.75         (((k2_relat_1 @ X33) != (X32))
% 4.56/4.75          | (v2_funct_2 @ X33 @ X32)
% 4.56/4.75          | ~ (v5_relat_1 @ X33 @ X32)
% 4.56/4.75          | ~ (v1_relat_1 @ X33))),
% 4.56/4.75      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.56/4.75  thf('95', plain,
% 4.56/4.75      (![X33 : $i]:
% 4.56/4.75         (~ (v1_relat_1 @ X33)
% 4.56/4.75          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 4.56/4.75          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 4.56/4.75      inference('simplify', [status(thm)], ['94'])).
% 4.56/4.75  thf('96', plain,
% 4.56/4.75      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 4.56/4.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.56/4.75  thf('97', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 4.56/4.75      inference('simplify', [status(thm)], ['96'])).
% 4.56/4.75  thf('98', plain,
% 4.56/4.75      (![X15 : $i, X16 : $i]:
% 4.56/4.75         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.56/4.75          | (v5_relat_1 @ X15 @ X16)
% 4.56/4.75          | ~ (v1_relat_1 @ X15))),
% 4.56/4.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.56/4.75  thf('99', plain,
% 4.56/4.75      (![X0 : $i]:
% 4.56/4.75         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.56/4.75      inference('sup-', [status(thm)], ['97', '98'])).
% 4.56/4.75  thf('100', plain,
% 4.56/4.75      (![X33 : $i]:
% 4.56/4.75         ((v2_funct_2 @ X33 @ (k2_relat_1 @ X33)) | ~ (v1_relat_1 @ X33))),
% 4.56/4.75      inference('clc', [status(thm)], ['95', '99'])).
% 4.56/4.75  thf('101', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.56/4.75      inference('sup+', [status(thm)], ['93', '100'])).
% 4.56/4.75  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 4.56/4.75      inference('demod', [status(thm)], ['81', '82'])).
% 4.56/4.75  thf('103', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.56/4.75      inference('demod', [status(thm)], ['101', '102'])).
% 4.56/4.75  thf('104', plain, ($false), inference('demod', [status(thm)], ['56', '103'])).
% 4.56/4.75  
% 4.56/4.75  % SZS output end Refutation
% 4.56/4.75  
% 4.56/4.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
