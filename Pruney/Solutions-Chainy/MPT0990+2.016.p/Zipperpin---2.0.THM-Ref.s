%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PiUBm2h7hC

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:56 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 530 expanded)
%              Number of leaves         :   43 ( 181 expanded)
%              Depth                    :   25
%              Number of atoms          : 1926 (10183 expanded)
%              Number of equality atoms :  112 ( 665 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('27',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('28',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['45','48'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('51',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('55',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('57',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('58',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('59',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('65',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('68',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('69',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('70',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('78',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('79',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('80',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['74','77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['67','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['87','90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['63','113'])).

thf('115',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('120',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('122',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X41 ) ) )
      | ( ( k5_relat_1 @ X42 @ ( k2_funct_1 @ X42 ) )
        = ( k6_partfun1 @ X43 ) )
      | ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X43 @ X41 @ X42 )
       != X41 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('123',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('127',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('128',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('129',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('132',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('136',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('140',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['129','145'])).

thf('147',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['134','135'])).

thf('148',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('149',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['146','153','154','155','156'])).

thf('158',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['126','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','161','162','163'])).

thf('165',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('173',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','40','55','168','169','170','171','172'])).

thf('174',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['173','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PiUBm2h7hC
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.72/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.90  % Solved by: fo/fo7.sh
% 0.72/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.90  % done 627 iterations in 0.441s
% 0.72/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.90  % SZS output start Refutation
% 0.72/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.72/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.90  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.72/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.90  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.72/0.90  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.72/0.90  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.72/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.90  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.72/0.90  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.72/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.90  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.72/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.90  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.72/0.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.72/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.72/0.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.72/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.90  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.72/0.90  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.72/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.90  thf(t36_funct_2, conjecture,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.72/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.72/0.90       ( ![D:$i]:
% 0.72/0.90         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.72/0.90             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.72/0.90           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.72/0.90               ( r2_relset_1 @
% 0.72/0.90                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.72/0.90                 ( k6_partfun1 @ A ) ) & 
% 0.72/0.90               ( v2_funct_1 @ C ) ) =>
% 0.72/0.90             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.72/0.90               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.72/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.90        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.72/0.90            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.72/0.90          ( ![D:$i]:
% 0.72/0.90            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.72/0.90                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.72/0.90              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.72/0.90                  ( r2_relset_1 @
% 0.72/0.90                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.72/0.90                    ( k6_partfun1 @ A ) ) & 
% 0.72/0.90                  ( v2_funct_1 @ C ) ) =>
% 0.72/0.90                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.72/0.90                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.72/0.90    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.72/0.90  thf('0', plain,
% 0.72/0.90      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.72/0.90        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.72/0.90        (k6_partfun1 @ sk_A))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('1', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('2', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(redefinition_k1_partfun1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.72/0.90     ( ( ( v1_funct_1 @ E ) & 
% 0.72/0.90         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.72/0.90         ( v1_funct_1 @ F ) & 
% 0.72/0.90         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.72/0.90       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.72/0.90  thf('3', plain,
% 0.72/0.90      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.72/0.90         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.72/0.90          | ~ (v1_funct_1 @ X34)
% 0.72/0.90          | ~ (v1_funct_1 @ X37)
% 0.72/0.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.72/0.90          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 0.72/0.90              = (k5_relat_1 @ X34 @ X37)))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.72/0.90  thf('4', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.72/0.90            = (k5_relat_1 @ sk_C @ X0))
% 0.72/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ sk_C))),
% 0.72/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.72/0.90  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('6', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.72/0.90            = (k5_relat_1 @ sk_C @ X0))
% 0.72/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.72/0.90          | ~ (v1_funct_1 @ X0))),
% 0.72/0.90      inference('demod', [status(thm)], ['4', '5'])).
% 0.72/0.90  thf('7', plain,
% 0.72/0.90      ((~ (v1_funct_1 @ sk_D)
% 0.72/0.90        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.72/0.90            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['1', '6'])).
% 0.72/0.90  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('9', plain,
% 0.72/0.90      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.72/0.90         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['7', '8'])).
% 0.72/0.90  thf('10', plain,
% 0.72/0.90      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.72/0.90        (k6_partfun1 @ sk_A))),
% 0.72/0.90      inference('demod', [status(thm)], ['0', '9'])).
% 0.72/0.90  thf('11', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('12', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(dt_k1_partfun1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.72/0.90     ( ( ( v1_funct_1 @ E ) & 
% 0.72/0.90         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.72/0.90         ( v1_funct_1 @ F ) & 
% 0.72/0.90         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.72/0.90       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.72/0.90         ( m1_subset_1 @
% 0.72/0.90           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.72/0.90           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.72/0.90  thf('13', plain,
% 0.72/0.90      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.72/0.90         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.72/0.90          | ~ (v1_funct_1 @ X26)
% 0.72/0.90          | ~ (v1_funct_1 @ X29)
% 0.72/0.90          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.72/0.90          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.72/0.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.72/0.90  thf('14', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.72/0.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.72/0.90          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.72/0.90          | ~ (v1_funct_1 @ X1)
% 0.72/0.90          | ~ (v1_funct_1 @ sk_C))),
% 0.72/0.90      inference('sup-', [status(thm)], ['12', '13'])).
% 0.72/0.90  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('16', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.72/0.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.72/0.90          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.72/0.90          | ~ (v1_funct_1 @ X1))),
% 0.72/0.90      inference('demod', [status(thm)], ['14', '15'])).
% 0.72/0.90  thf('17', plain,
% 0.72/0.90      ((~ (v1_funct_1 @ sk_D)
% 0.72/0.90        | (m1_subset_1 @ 
% 0.72/0.90           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.72/0.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['11', '16'])).
% 0.72/0.90  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('19', plain,
% 0.72/0.90      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.72/0.90         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['7', '8'])).
% 0.72/0.90  thf('20', plain,
% 0.72/0.90      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.72/0.90  thf(redefinition_r2_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.90     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.72/0.90         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.72/0.90       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.72/0.90  thf('21', plain,
% 0.72/0.90      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.72/0.90         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.72/0.90          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.72/0.90          | ((X22) = (X25))
% 0.72/0.90          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.72/0.90  thf('22', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.72/0.90          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.72/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.90  thf('23', plain,
% 0.72/0.90      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.72/0.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.72/0.90        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['10', '22'])).
% 0.72/0.90  thf(dt_k6_partfun1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( m1_subset_1 @
% 0.72/0.90         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.72/0.90       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.72/0.90  thf('24', plain,
% 0.72/0.90      (![X33 : $i]:
% 0.72/0.90         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.72/0.90          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.72/0.90  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.72/0.90      inference('demod', [status(thm)], ['23', '24'])).
% 0.72/0.90  thf(dt_k2_funct_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.72/0.90       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.72/0.90         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.72/0.90  thf('26', plain,
% 0.72/0.90      (![X10 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.72/0.90          | ~ (v1_funct_1 @ X10)
% 0.72/0.90          | ~ (v1_relat_1 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.72/0.90  thf(t61_funct_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.72/0.90       ( ( v2_funct_1 @ A ) =>
% 0.72/0.90         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.72/0.90             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.72/0.90           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.72/0.90             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.72/0.90  thf('27', plain,
% 0.72/0.90      (![X12 : $i]:
% 0.72/0.90         (~ (v2_funct_1 @ X12)
% 0.72/0.90          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 0.72/0.90              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 0.72/0.90          | ~ (v1_funct_1 @ X12)
% 0.72/0.90          | ~ (v1_relat_1 @ X12))),
% 0.72/0.90      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.72/0.90  thf(redefinition_k6_partfun1, axiom,
% 0.72/0.90    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.72/0.90  thf('28', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.72/0.90  thf('29', plain,
% 0.72/0.90      (![X12 : $i]:
% 0.72/0.90         (~ (v2_funct_1 @ X12)
% 0.72/0.90          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 0.72/0.90              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 0.72/0.90          | ~ (v1_funct_1 @ X12)
% 0.72/0.90          | ~ (v1_relat_1 @ X12))),
% 0.72/0.90      inference('demod', [status(thm)], ['27', '28'])).
% 0.72/0.90  thf(t55_relat_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ A ) =>
% 0.72/0.90       ( ![B:$i]:
% 0.72/0.90         ( ( v1_relat_1 @ B ) =>
% 0.72/0.90           ( ![C:$i]:
% 0.72/0.90             ( ( v1_relat_1 @ C ) =>
% 0.72/0.90               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.72/0.90                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.72/0.90  thf('30', plain,
% 0.72/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X2)
% 0.72/0.90          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.72/0.90              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.72/0.90          | ~ (v1_relat_1 @ X4)
% 0.72/0.90          | ~ (v1_relat_1 @ X3))),
% 0.72/0.90      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.72/0.90  thf('31', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.72/0.90            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.72/0.90          | ~ (v1_relat_1 @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['29', '30'])).
% 0.72/0.90  thf('32', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.72/0.90              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['31'])).
% 0.72/0.90  thf('33', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.72/0.90              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X1))),
% 0.72/0.90      inference('sup-', [status(thm)], ['26', '32'])).
% 0.72/0.90  thf('34', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X1)
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.72/0.90              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['33'])).
% 0.72/0.90  thf('35', plain,
% 0.72/0.90      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 0.72/0.90          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.72/0.90        | ~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | ~ (v2_funct_1 @ sk_C)
% 0.72/0.90        | ~ (v1_relat_1 @ sk_D))),
% 0.72/0.90      inference('sup+', [status(thm)], ['25', '34'])).
% 0.72/0.90  thf('36', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(redefinition_k2_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.72/0.90  thf('37', plain,
% 0.72/0.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.72/0.90         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.72/0.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.72/0.90  thf('38', plain,
% 0.72/0.90      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.72/0.90      inference('sup-', [status(thm)], ['36', '37'])).
% 0.72/0.90  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('40', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.72/0.90      inference('sup+', [status(thm)], ['38', '39'])).
% 0.72/0.90  thf('41', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(cc2_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.72/0.90  thf('42', plain,
% 0.72/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.72/0.90         ((v4_relat_1 @ X16 @ X17)
% 0.72/0.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.72/0.90  thf('43', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.72/0.90      inference('sup-', [status(thm)], ['41', '42'])).
% 0.72/0.90  thf(d18_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ B ) =>
% 0.72/0.90       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.72/0.90  thf('44', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v4_relat_1 @ X0 @ X1)
% 0.72/0.90          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.72/0.90  thf('45', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.72/0.90      inference('sup-', [status(thm)], ['43', '44'])).
% 0.72/0.90  thf('46', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(cc1_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( v1_relat_1 @ C ) ))).
% 0.72/0.90  thf('47', plain,
% 0.72/0.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.90         ((v1_relat_1 @ X13)
% 0.72/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.72/0.90  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.72/0.90      inference('sup-', [status(thm)], ['46', '47'])).
% 0.72/0.90  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.72/0.90      inference('demod', [status(thm)], ['45', '48'])).
% 0.72/0.90  thf(t77_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ B ) =>
% 0.72/0.90       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.72/0.90         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.72/0.90  thf('50', plain,
% 0.72/0.90      (![X7 : $i, X8 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.72/0.90          | ((k5_relat_1 @ (k6_relat_1 @ X8) @ X7) = (X7))
% 0.72/0.90          | ~ (v1_relat_1 @ X7))),
% 0.72/0.90      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.72/0.90  thf('51', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.72/0.90  thf('52', plain,
% 0.72/0.90      (![X7 : $i, X8 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ X8) @ X7) = (X7))
% 0.72/0.90          | ~ (v1_relat_1 @ X7))),
% 0.72/0.90      inference('demod', [status(thm)], ['50', '51'])).
% 0.72/0.90  thf('53', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_D)
% 0.72/0.90        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['49', '52'])).
% 0.72/0.90  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 0.72/0.90      inference('sup-', [status(thm)], ['46', '47'])).
% 0.72/0.90  thf('55', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['53', '54'])).
% 0.72/0.90  thf('56', plain,
% 0.72/0.90      (![X10 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.72/0.90          | ~ (v1_funct_1 @ X10)
% 0.72/0.90          | ~ (v1_relat_1 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.72/0.90  thf(t55_funct_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.72/0.90       ( ( v2_funct_1 @ A ) =>
% 0.72/0.90         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.72/0.90           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.72/0.90  thf('57', plain,
% 0.72/0.90      (![X11 : $i]:
% 0.72/0.90         (~ (v2_funct_1 @ X11)
% 0.72/0.90          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 0.72/0.90          | ~ (v1_funct_1 @ X11)
% 0.72/0.90          | ~ (v1_relat_1 @ X11))),
% 0.72/0.90      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.72/0.90  thf(t80_relat_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ A ) =>
% 0.72/0.90       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.72/0.90  thf('58', plain,
% 0.72/0.90      (![X9 : $i]:
% 0.72/0.90         (((k5_relat_1 @ X9 @ (k6_relat_1 @ (k2_relat_1 @ X9))) = (X9))
% 0.72/0.90          | ~ (v1_relat_1 @ X9))),
% 0.72/0.90      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.72/0.90  thf('59', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.72/0.90  thf('60', plain,
% 0.72/0.90      (![X9 : $i]:
% 0.72/0.90         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 0.72/0.90          | ~ (v1_relat_1 @ X9))),
% 0.72/0.90      inference('demod', [status(thm)], ['58', '59'])).
% 0.72/0.90  thf('61', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.72/0.90            = (k2_funct_1 @ X0))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['57', '60'])).
% 0.72/0.90  thf('62', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.72/0.90              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['56', '61'])).
% 0.72/0.90  thf('63', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.72/0.90            = (k2_funct_1 @ X0))
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['62'])).
% 0.72/0.90  thf('64', plain,
% 0.72/0.90      (![X10 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.72/0.90          | ~ (v1_funct_1 @ X10)
% 0.72/0.90          | ~ (v1_relat_1 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.72/0.90  thf('65', plain,
% 0.72/0.90      (![X10 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.72/0.90          | ~ (v1_funct_1 @ X10)
% 0.72/0.90          | ~ (v1_relat_1 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.72/0.90  thf('66', plain,
% 0.72/0.90      (![X10 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.72/0.90          | ~ (v1_funct_1 @ X10)
% 0.72/0.90          | ~ (v1_relat_1 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.72/0.90  thf('67', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.72/0.90      inference('sup+', [status(thm)], ['38', '39'])).
% 0.72/0.90  thf('68', plain,
% 0.72/0.90      (![X10 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.72/0.90          | ~ (v1_funct_1 @ X10)
% 0.72/0.90          | ~ (v1_relat_1 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.72/0.90  thf('69', plain,
% 0.72/0.90      (![X11 : $i]:
% 0.72/0.90         (~ (v2_funct_1 @ X11)
% 0.72/0.90          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 0.72/0.90          | ~ (v1_funct_1 @ X11)
% 0.72/0.90          | ~ (v1_relat_1 @ X11))),
% 0.72/0.90      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.72/0.90  thf('70', plain,
% 0.72/0.90      (![X33 : $i]:
% 0.72/0.90         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.72/0.90          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.72/0.90  thf('71', plain,
% 0.72/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.72/0.90         ((v4_relat_1 @ X16 @ X17)
% 0.72/0.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.72/0.90  thf('72', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 0.72/0.90      inference('sup-', [status(thm)], ['70', '71'])).
% 0.72/0.90  thf('73', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v4_relat_1 @ X0 @ X1)
% 0.72/0.90          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.72/0.90  thf('74', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.72/0.90          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['72', '73'])).
% 0.72/0.90  thf('75', plain,
% 0.72/0.90      (![X33 : $i]:
% 0.72/0.90         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.72/0.90          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.72/0.90  thf('76', plain,
% 0.72/0.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.90         ((v1_relat_1 @ X13)
% 0.72/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.72/0.90  thf('77', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['75', '76'])).
% 0.72/0.90  thf(t71_relat_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.72/0.90       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.72/0.90  thf('78', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.72/0.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.72/0.90  thf('79', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.72/0.90  thf('80', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.72/0.90      inference('demod', [status(thm)], ['78', '79'])).
% 0.72/0.90  thf('81', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.72/0.90      inference('demod', [status(thm)], ['74', '77', '80'])).
% 0.72/0.90  thf('82', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.72/0.90          | (v4_relat_1 @ X0 @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.72/0.90  thf('83', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['81', '82'])).
% 0.72/0.90  thf('84', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['69', '83'])).
% 0.72/0.90  thf('85', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['68', '84'])).
% 0.72/0.90  thf('86', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.72/0.90          | ~ (v2_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['85'])).
% 0.72/0.90  thf('87', plain,
% 0.72/0.90      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 0.72/0.90        | ~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | ~ (v2_funct_1 @ sk_C))),
% 0.72/0.90      inference('sup+', [status(thm)], ['67', '86'])).
% 0.72/0.90  thf('88', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('89', plain,
% 0.72/0.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.90         ((v1_relat_1 @ X13)
% 0.72/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.72/0.90  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('93', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 0.72/0.90      inference('demod', [status(thm)], ['87', '90', '91', '92'])).
% 0.72/0.90  thf('94', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v4_relat_1 @ X0 @ X1)
% 0.72/0.90          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.72/0.90  thf('95', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.72/0.90        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.72/0.90      inference('sup-', [status(thm)], ['93', '94'])).
% 0.72/0.90  thf('96', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.72/0.90      inference('sup-', [status(thm)], ['66', '95'])).
% 0.72/0.90  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('99', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.72/0.90      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.72/0.90  thf('100', plain,
% 0.72/0.90      (![X7 : $i, X8 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ X8) @ X7) = (X7))
% 0.72/0.90          | ~ (v1_relat_1 @ X7))),
% 0.72/0.90      inference('demod', [status(thm)], ['50', '51'])).
% 0.72/0.90  thf('101', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.72/0.90        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.72/0.90            = (k2_funct_1 @ sk_C)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['99', '100'])).
% 0.72/0.90  thf('102', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.72/0.90            = (k2_funct_1 @ sk_C)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['65', '101'])).
% 0.72/0.90  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('105', plain,
% 0.72/0.90      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.72/0.90         = (k2_funct_1 @ sk_C))),
% 0.72/0.90      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.72/0.90  thf('106', plain,
% 0.72/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X2)
% 0.72/0.90          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.72/0.90              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.72/0.90          | ~ (v1_relat_1 @ X4)
% 0.72/0.90          | ~ (v1_relat_1 @ X3))),
% 0.72/0.90      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.72/0.90  thf('107', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.72/0.90            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.72/0.90               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.72/0.90          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['105', '106'])).
% 0.72/0.90  thf('108', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['75', '76'])).
% 0.72/0.90  thf('109', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.72/0.90            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.72/0.90               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.72/0.90      inference('demod', [status(thm)], ['107', '108'])).
% 0.72/0.90  thf('110', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ sk_C)
% 0.72/0.90          | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.72/0.90              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.72/0.90                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['64', '109'])).
% 0.72/0.90  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('113', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X0)
% 0.72/0.90          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.72/0.90              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.72/0.90                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.72/0.90      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.72/0.90  thf('114', plain,
% 0.72/0.90      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.72/0.90          (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.72/0.90          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 0.72/0.90        | ~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | ~ (v2_funct_1 @ sk_C)
% 0.72/0.90        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 0.72/0.90      inference('sup+', [status(thm)], ['63', '113'])).
% 0.72/0.90  thf('115', plain,
% 0.72/0.90      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.72/0.90         = (k2_funct_1 @ sk_C))),
% 0.72/0.90      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.72/0.90  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('119', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['75', '76'])).
% 0.72/0.90  thf('120', plain,
% 0.72/0.90      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.72/0.90         = (k2_funct_1 @ sk_C))),
% 0.72/0.90      inference('demod', [status(thm)],
% 0.72/0.90                ['114', '115', '116', '117', '118', '119'])).
% 0.72/0.90  thf('121', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(t35_funct_2, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.72/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.72/0.90       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.72/0.90         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.72/0.90           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.72/0.90             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.72/0.90  thf('122', plain,
% 0.72/0.90      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.72/0.90         (((X41) = (k1_xboole_0))
% 0.72/0.90          | ~ (v1_funct_1 @ X42)
% 0.72/0.90          | ~ (v1_funct_2 @ X42 @ X43 @ X41)
% 0.72/0.90          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 0.72/0.90          | ((k5_relat_1 @ X42 @ (k2_funct_1 @ X42)) = (k6_partfun1 @ X43))
% 0.72/0.90          | ~ (v2_funct_1 @ X42)
% 0.72/0.90          | ((k2_relset_1 @ X43 @ X41 @ X42) != (X41)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.72/0.90  thf('123', plain,
% 0.72/0.90      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.72/0.90        | ~ (v2_funct_1 @ sk_C)
% 0.72/0.90        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.72/0.90        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | ((sk_B) = (k1_xboole_0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['121', '122'])).
% 0.72/0.90  thf('124', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('126', plain,
% 0.72/0.90      (![X10 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.72/0.90          | ~ (v1_funct_1 @ X10)
% 0.72/0.90          | ~ (v1_relat_1 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.72/0.90  thf('127', plain,
% 0.72/0.90      (![X12 : $i]:
% 0.72/0.90         (~ (v2_funct_1 @ X12)
% 0.72/0.90          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 0.72/0.90              = (k6_relat_1 @ (k1_relat_1 @ X12)))
% 0.72/0.90          | ~ (v1_funct_1 @ X12)
% 0.72/0.90          | ~ (v1_relat_1 @ X12))),
% 0.72/0.90      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.72/0.90  thf('128', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.72/0.90  thf('129', plain,
% 0.72/0.90      (![X12 : $i]:
% 0.72/0.90         (~ (v2_funct_1 @ X12)
% 0.72/0.90          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 0.72/0.90              = (k6_partfun1 @ (k1_relat_1 @ X12)))
% 0.72/0.90          | ~ (v1_funct_1 @ X12)
% 0.72/0.90          | ~ (v1_relat_1 @ X12))),
% 0.72/0.90      inference('demod', [status(thm)], ['127', '128'])).
% 0.72/0.90  thf('130', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('131', plain,
% 0.72/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.72/0.90         ((v4_relat_1 @ X16 @ X17)
% 0.72/0.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.72/0.90  thf('132', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.72/0.90      inference('sup-', [status(thm)], ['130', '131'])).
% 0.72/0.90  thf('133', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v4_relat_1 @ X0 @ X1)
% 0.72/0.90          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.72/0.90  thf('134', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.72/0.90      inference('sup-', [status(thm)], ['132', '133'])).
% 0.72/0.90  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('136', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.72/0.90      inference('demod', [status(thm)], ['134', '135'])).
% 0.72/0.90  thf('137', plain,
% 0.72/0.90      (![X7 : $i, X8 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ X8) @ X7) = (X7))
% 0.72/0.90          | ~ (v1_relat_1 @ X7))),
% 0.72/0.90      inference('demod', [status(thm)], ['50', '51'])).
% 0.72/0.90  thf('138', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['136', '137'])).
% 0.72/0.90  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('140', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 0.72/0.90      inference('demod', [status(thm)], ['138', '139'])).
% 0.72/0.90  thf('141', plain,
% 0.72/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X2)
% 0.72/0.90          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.72/0.90              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.72/0.90          | ~ (v1_relat_1 @ X4)
% 0.72/0.90          | ~ (v1_relat_1 @ X3))),
% 0.72/0.90      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.72/0.90  thf('142', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k5_relat_1 @ sk_C @ X0)
% 0.72/0.90            = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 0.72/0.90          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ sk_C))),
% 0.72/0.90      inference('sup+', [status(thm)], ['140', '141'])).
% 0.72/0.90  thf('143', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['75', '76'])).
% 0.72/0.90  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('145', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k5_relat_1 @ sk_C @ X0)
% 0.72/0.90            = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.72/0.90  thf('146', plain,
% 0.72/0.90      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.72/0.90          = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 0.72/0.90             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 0.72/0.90        | ~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | ~ (v2_funct_1 @ sk_C)
% 0.72/0.90        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['129', '145'])).
% 0.72/0.90  thf('147', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.72/0.90      inference('demod', [status(thm)], ['134', '135'])).
% 0.72/0.90  thf('148', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.72/0.90      inference('demod', [status(thm)], ['78', '79'])).
% 0.72/0.90  thf('149', plain,
% 0.72/0.90      (![X7 : $i, X8 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ X8) @ X7) = (X7))
% 0.72/0.90          | ~ (v1_relat_1 @ X7))),
% 0.72/0.90      inference('demod', [status(thm)], ['50', '51'])).
% 0.72/0.90  thf('150', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (r1_tarski @ X0 @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 0.72/0.90              = (k6_partfun1 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['148', '149'])).
% 0.72/0.90  thf('151', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['75', '76'])).
% 0.72/0.90  thf('152', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (r1_tarski @ X0 @ X1)
% 0.72/0.90          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 0.72/0.90              = (k6_partfun1 @ X0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['150', '151'])).
% 0.72/0.90  thf('153', plain,
% 0.72/0.90      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 0.72/0.90         (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.72/0.90         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['147', '152'])).
% 0.72/0.90  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('157', plain,
% 0.72/0.90      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.72/0.90          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.72/0.90        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.72/0.90      inference('demod', [status(thm)], ['146', '153', '154', '155', '156'])).
% 0.72/0.90  thf('158', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.72/0.90            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['126', '157'])).
% 0.72/0.90  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('161', plain,
% 0.72/0.90      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.72/0.90         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 0.72/0.90      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.72/0.90  thf('162', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('164', plain,
% 0.72/0.90      ((((sk_B) != (sk_B))
% 0.72/0.90        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.72/0.90        | ((sk_B) = (k1_xboole_0)))),
% 0.72/0.90      inference('demod', [status(thm)],
% 0.72/0.90                ['123', '124', '125', '161', '162', '163'])).
% 0.72/0.90  thf('165', plain,
% 0.72/0.90      ((((sk_B) = (k1_xboole_0))
% 0.72/0.90        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['164'])).
% 0.72/0.90  thf('166', plain, (((sk_B) != (k1_xboole_0))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('167', plain,
% 0.72/0.90      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 0.72/0.90  thf('168', plain,
% 0.72/0.90      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.72/0.90         = (k2_funct_1 @ sk_C))),
% 0.72/0.90      inference('demod', [status(thm)], ['120', '167'])).
% 0.72/0.90  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.90  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('172', plain, ((v1_relat_1 @ sk_D)),
% 0.72/0.90      inference('sup-', [status(thm)], ['46', '47'])).
% 0.72/0.90  thf('173', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.72/0.90      inference('demod', [status(thm)],
% 0.72/0.90                ['35', '40', '55', '168', '169', '170', '171', '172'])).
% 0.72/0.90  thf('174', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('175', plain, ($false),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['173', '174'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
