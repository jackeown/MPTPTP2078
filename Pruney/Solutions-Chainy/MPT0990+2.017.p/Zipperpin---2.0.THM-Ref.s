%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3oc0JlQswb

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:56 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 217 expanded)
%              Number of leaves         :   41 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          : 1149 (4563 expanded)
%              Number of equality atoms :   58 ( 297 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
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
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
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
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('28',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('51',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X6 ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['61','64'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('68',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ X7 @ ( k6_partfun1 @ X8 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('75',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['62','63'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('84',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','40','55','79','80','81','82','83'])).

thf('85',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3oc0JlQswb
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.70  % Solved by: fo/fo7.sh
% 0.48/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.70  % done 268 iterations in 0.252s
% 0.48/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.70  % SZS output start Refutation
% 0.48/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.70  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.48/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.48/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.48/0.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.48/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.70  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.48/0.70  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.48/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.48/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.48/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.48/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.48/0.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.48/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.71  thf(t36_funct_2, conjecture,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.48/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.71       ( ![D:$i]:
% 0.48/0.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.48/0.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.48/0.71           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.48/0.71               ( r2_relset_1 @
% 0.48/0.71                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.48/0.71                 ( k6_partfun1 @ A ) ) & 
% 0.48/0.71               ( v2_funct_1 @ C ) ) =>
% 0.48/0.71             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.48/0.71               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.48/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.48/0.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.48/0.71            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.71          ( ![D:$i]:
% 0.48/0.71            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.48/0.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.48/0.71              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.48/0.71                  ( r2_relset_1 @
% 0.48/0.71                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.48/0.71                    ( k6_partfun1 @ A ) ) & 
% 0.48/0.71                  ( v2_funct_1 @ C ) ) =>
% 0.48/0.71                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.48/0.71                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.48/0.71    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.48/0.71  thf('0', plain,
% 0.48/0.71      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.48/0.71        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.48/0.71        (k6_partfun1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('1', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('2', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(redefinition_k1_partfun1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.48/0.71     ( ( ( v1_funct_1 @ E ) & 
% 0.48/0.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.48/0.71         ( v1_funct_1 @ F ) & 
% 0.48/0.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.48/0.71       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.48/0.71  thf('3', plain,
% 0.48/0.71      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.48/0.71          | ~ (v1_funct_1 @ X33)
% 0.48/0.71          | ~ (v1_funct_1 @ X36)
% 0.48/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.48/0.71          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 0.48/0.71              = (k5_relat_1 @ X33 @ X36)))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.48/0.71  thf('4', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.71         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.48/0.71            = (k5_relat_1 @ sk_C @ X0))
% 0.48/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.48/0.71          | ~ (v1_funct_1 @ X0)
% 0.48/0.71          | ~ (v1_funct_1 @ sk_C))),
% 0.48/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('6', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.71         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.48/0.71            = (k5_relat_1 @ sk_C @ X0))
% 0.48/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.48/0.71          | ~ (v1_funct_1 @ X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.48/0.71  thf('7', plain,
% 0.48/0.71      ((~ (v1_funct_1 @ sk_D)
% 0.48/0.71        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.48/0.71            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['1', '6'])).
% 0.48/0.71  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('9', plain,
% 0.48/0.71      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.48/0.71         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.71  thf('10', plain,
% 0.48/0.71      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.48/0.71        (k6_partfun1 @ sk_A))),
% 0.48/0.71      inference('demod', [status(thm)], ['0', '9'])).
% 0.48/0.71  thf('11', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('12', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(dt_k1_partfun1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.48/0.71     ( ( ( v1_funct_1 @ E ) & 
% 0.48/0.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.48/0.71         ( v1_funct_1 @ F ) & 
% 0.48/0.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.48/0.71       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.48/0.71         ( m1_subset_1 @
% 0.48/0.71           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.48/0.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.48/0.71  thf('13', plain,
% 0.48/0.71      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.48/0.71          | ~ (v1_funct_1 @ X25)
% 0.48/0.71          | ~ (v1_funct_1 @ X28)
% 0.48/0.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.48/0.71          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 0.48/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 0.48/0.71      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.48/0.71  thf('14', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.71         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.48/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.48/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.48/0.71          | ~ (v1_funct_1 @ X1)
% 0.48/0.71          | ~ (v1_funct_1 @ sk_C))),
% 0.48/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.48/0.71  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('16', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.71         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.48/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.48/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.48/0.71          | ~ (v1_funct_1 @ X1))),
% 0.48/0.71      inference('demod', [status(thm)], ['14', '15'])).
% 0.48/0.71  thf('17', plain,
% 0.48/0.71      ((~ (v1_funct_1 @ sk_D)
% 0.48/0.71        | (m1_subset_1 @ 
% 0.48/0.71           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.48/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['11', '16'])).
% 0.48/0.71  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('19', plain,
% 0.48/0.71      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.48/0.71         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.71  thf('20', plain,
% 0.48/0.71      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.48/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.48/0.71      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.48/0.71  thf(redefinition_r2_relset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.71     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.48/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.71       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.48/0.71  thf('21', plain,
% 0.48/0.71      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.48/0.71          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.48/0.71          | ((X21) = (X24))
% 0.48/0.71          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.48/0.71  thf('22', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.48/0.71          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.48/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.71  thf('23', plain,
% 0.48/0.71      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.48/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.48/0.71        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['10', '22'])).
% 0.48/0.71  thf(dt_k6_partfun1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( m1_subset_1 @
% 0.48/0.71         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.48/0.71       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.48/0.71  thf('24', plain,
% 0.48/0.71      (![X32 : $i]:
% 0.48/0.71         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.48/0.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.48/0.71      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.48/0.71  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.48/0.71      inference('demod', [status(thm)], ['23', '24'])).
% 0.48/0.71  thf(dt_k2_funct_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.48/0.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.48/0.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.48/0.71  thf('26', plain,
% 0.48/0.71      (![X9 : $i]:
% 0.48/0.71         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.48/0.71          | ~ (v1_funct_1 @ X9)
% 0.48/0.71          | ~ (v1_relat_1 @ X9))),
% 0.48/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.48/0.71  thf(t61_funct_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.48/0.71       ( ( v2_funct_1 @ A ) =>
% 0.48/0.71         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.48/0.71             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.48/0.71           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.48/0.71             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.48/0.71  thf('27', plain,
% 0.48/0.71      (![X11 : $i]:
% 0.48/0.71         (~ (v2_funct_1 @ X11)
% 0.48/0.71          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 0.48/0.71              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 0.48/0.71          | ~ (v1_funct_1 @ X11)
% 0.48/0.71          | ~ (v1_relat_1 @ X11))),
% 0.48/0.71      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.48/0.71  thf(redefinition_k6_partfun1, axiom,
% 0.48/0.71    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.48/0.71  thf('28', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.48/0.71  thf('29', plain,
% 0.48/0.71      (![X11 : $i]:
% 0.48/0.71         (~ (v2_funct_1 @ X11)
% 0.48/0.71          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 0.48/0.71              = (k6_partfun1 @ (k2_relat_1 @ X11)))
% 0.48/0.71          | ~ (v1_funct_1 @ X11)
% 0.48/0.71          | ~ (v1_relat_1 @ X11))),
% 0.48/0.71      inference('demod', [status(thm)], ['27', '28'])).
% 0.48/0.71  thf(t55_relat_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ A ) =>
% 0.48/0.71       ( ![B:$i]:
% 0.48/0.71         ( ( v1_relat_1 @ B ) =>
% 0.48/0.71           ( ![C:$i]:
% 0.48/0.71             ( ( v1_relat_1 @ C ) =>
% 0.48/0.71               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.48/0.71                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.48/0.71  thf('30', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.71         (~ (v1_relat_1 @ X2)
% 0.48/0.71          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.48/0.71              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.48/0.71          | ~ (v1_relat_1 @ X4)
% 0.48/0.71          | ~ (v1_relat_1 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.48/0.71  thf('31', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.48/0.71            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.48/0.71          | ~ (v1_relat_1 @ X0)
% 0.48/0.71          | ~ (v1_funct_1 @ X0)
% 0.48/0.71          | ~ (v2_funct_1 @ X0)
% 0.48/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.48/0.71          | ~ (v1_relat_1 @ X1)
% 0.48/0.71          | ~ (v1_relat_1 @ X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['29', '30'])).
% 0.48/0.71  thf('32', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (~ (v1_relat_1 @ X1)
% 0.48/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.48/0.71          | ~ (v2_funct_1 @ X0)
% 0.48/0.71          | ~ (v1_funct_1 @ X0)
% 0.48/0.71          | ~ (v1_relat_1 @ X0)
% 0.48/0.71          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.48/0.71              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 0.48/0.71      inference('simplify', [status(thm)], ['31'])).
% 0.48/0.71  thf('33', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (~ (v1_relat_1 @ X0)
% 0.48/0.71          | ~ (v1_funct_1 @ X0)
% 0.48/0.71          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.48/0.71              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.48/0.71          | ~ (v1_relat_1 @ X0)
% 0.48/0.71          | ~ (v1_funct_1 @ X0)
% 0.48/0.71          | ~ (v2_funct_1 @ X0)
% 0.48/0.71          | ~ (v1_relat_1 @ X1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['26', '32'])).
% 0.48/0.71  thf('34', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (~ (v1_relat_1 @ X1)
% 0.48/0.71          | ~ (v2_funct_1 @ X0)
% 0.48/0.71          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.48/0.71              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.48/0.71          | ~ (v1_funct_1 @ X0)
% 0.48/0.71          | ~ (v1_relat_1 @ X0))),
% 0.48/0.71      inference('simplify', [status(thm)], ['33'])).
% 0.48/0.71  thf('35', plain,
% 0.48/0.71      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 0.48/0.71          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.48/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.48/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.48/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.48/0.71        | ~ (v1_relat_1 @ sk_D))),
% 0.48/0.71      inference('sup+', [status(thm)], ['25', '34'])).
% 0.48/0.71  thf('36', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.48/0.71  thf('37', plain,
% 0.48/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.71         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.48/0.71          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.48/0.71  thf('38', plain,
% 0.48/0.71      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.48/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.71  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('40', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.48/0.71      inference('sup+', [status(thm)], ['38', '39'])).
% 0.48/0.71  thf('41', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(cc2_relset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.48/0.71  thf('42', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.71         ((v4_relat_1 @ X15 @ X16)
% 0.48/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.48/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.71  thf('43', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.48/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.48/0.71  thf(d18_relat_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ B ) =>
% 0.48/0.71       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.48/0.71  thf('44', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (~ (v4_relat_1 @ X0 @ X1)
% 0.48/0.71          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.48/0.71          | ~ (v1_relat_1 @ X0))),
% 0.48/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.48/0.71  thf('45', plain,
% 0.48/0.71      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.71  thf('46', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(cc1_relset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.71       ( v1_relat_1 @ C ) ))).
% 0.48/0.71  thf('47', plain,
% 0.48/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.71         ((v1_relat_1 @ X12)
% 0.48/0.71          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.48/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.71  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.48/0.71      inference('sup-', [status(thm)], ['46', '47'])).
% 0.48/0.71  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.48/0.71      inference('demod', [status(thm)], ['45', '48'])).
% 0.48/0.71  thf(t77_relat_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ B ) =>
% 0.48/0.71       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.48/0.71         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.48/0.71  thf('50', plain,
% 0.48/0.71      (![X5 : $i, X6 : $i]:
% 0.48/0.71         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.48/0.71          | ((k5_relat_1 @ (k6_relat_1 @ X6) @ X5) = (X5))
% 0.48/0.71          | ~ (v1_relat_1 @ X5))),
% 0.48/0.71      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.48/0.71  thf('51', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.48/0.71  thf('52', plain,
% 0.48/0.71      (![X5 : $i, X6 : $i]:
% 0.48/0.71         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.48/0.71          | ((k5_relat_1 @ (k6_partfun1 @ X6) @ X5) = (X5))
% 0.48/0.71          | ~ (v1_relat_1 @ X5))),
% 0.48/0.71      inference('demod', [status(thm)], ['50', '51'])).
% 0.48/0.71  thf('53', plain,
% 0.48/0.71      ((~ (v1_relat_1 @ sk_D)
% 0.48/0.71        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['49', '52'])).
% 0.48/0.71  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 0.48/0.71      inference('sup-', [status(thm)], ['46', '47'])).
% 0.48/0.71  thf('55', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('56', plain,
% 0.48/0.71      (![X9 : $i]:
% 0.48/0.71         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.48/0.71          | ~ (v1_funct_1 @ X9)
% 0.48/0.71          | ~ (v1_relat_1 @ X9))),
% 0.48/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.48/0.71  thf('57', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('58', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.71         ((v4_relat_1 @ X15 @ X16)
% 0.48/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.48/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.71  thf('59', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.48/0.71      inference('sup-', [status(thm)], ['57', '58'])).
% 0.48/0.71  thf('60', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (~ (v4_relat_1 @ X0 @ X1)
% 0.48/0.71          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.48/0.71          | ~ (v1_relat_1 @ X0))),
% 0.48/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.48/0.71  thf('61', plain,
% 0.48/0.71      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['59', '60'])).
% 0.48/0.71  thf('62', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('63', plain,
% 0.48/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.71         ((v1_relat_1 @ X12)
% 0.48/0.71          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.48/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.71  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.48/0.71      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.71  thf('65', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.48/0.71      inference('demod', [status(thm)], ['61', '64'])).
% 0.48/0.71  thf(t55_funct_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.48/0.71       ( ( v2_funct_1 @ A ) =>
% 0.48/0.71         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.48/0.71           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.48/0.71  thf('66', plain,
% 0.48/0.71      (![X10 : $i]:
% 0.48/0.71         (~ (v2_funct_1 @ X10)
% 0.48/0.71          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.48/0.71          | ~ (v1_funct_1 @ X10)
% 0.48/0.71          | ~ (v1_relat_1 @ X10))),
% 0.48/0.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.48/0.71  thf(t79_relat_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ B ) =>
% 0.48/0.71       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.48/0.71         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.48/0.71  thf('67', plain,
% 0.48/0.71      (![X7 : $i, X8 : $i]:
% 0.48/0.71         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.48/0.71          | ((k5_relat_1 @ X7 @ (k6_relat_1 @ X8)) = (X7))
% 0.48/0.71          | ~ (v1_relat_1 @ X7))),
% 0.48/0.71      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.48/0.71  thf('68', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.48/0.71  thf('69', plain,
% 0.48/0.71      (![X7 : $i, X8 : $i]:
% 0.48/0.71         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.48/0.71          | ((k5_relat_1 @ X7 @ (k6_partfun1 @ X8)) = (X7))
% 0.48/0.71          | ~ (v1_relat_1 @ X7))),
% 0.48/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.48/0.71  thf('70', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.48/0.71          | ~ (v1_relat_1 @ X0)
% 0.48/0.71          | ~ (v1_funct_1 @ X0)
% 0.48/0.71          | ~ (v2_funct_1 @ X0)
% 0.48/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.48/0.71          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 0.48/0.71              = (k2_funct_1 @ X0)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['66', '69'])).
% 0.48/0.71  thf('71', plain,
% 0.48/0.71      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.48/0.71          = (k2_funct_1 @ sk_C))
% 0.48/0.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.48/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.48/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.48/0.71        | ~ (v1_relat_1 @ sk_C))),
% 0.48/0.71      inference('sup-', [status(thm)], ['65', '70'])).
% 0.48/0.71  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.48/0.71      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.71  thf('75', plain,
% 0.48/0.71      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.48/0.71          = (k2_funct_1 @ sk_C))
% 0.48/0.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.48/0.71      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.48/0.71  thf('76', plain,
% 0.48/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.48/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.48/0.71        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.48/0.71            = (k2_funct_1 @ sk_C)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['56', '75'])).
% 0.48/0.71  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.48/0.71      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.71  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('79', plain,
% 0.48/0.71      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.48/0.71         = (k2_funct_1 @ sk_C))),
% 0.48/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.48/0.71  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.48/0.71      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.71  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 0.48/0.71      inference('sup-', [status(thm)], ['46', '47'])).
% 0.48/0.71  thf('84', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.48/0.71      inference('demod', [status(thm)],
% 0.48/0.71                ['35', '40', '55', '79', '80', '81', '82', '83'])).
% 0.48/0.71  thf('85', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('86', plain, ($false),
% 0.48/0.71      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.48/0.71  
% 0.48/0.71  % SZS output end Refutation
% 0.48/0.71  
% 0.48/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
