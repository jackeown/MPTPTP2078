%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cW7vLAhckz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:08 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  343 (3075 expanded)
%              Number of leaves         :   49 ( 913 expanded)
%              Depth                    :   41
%              Number of atoms          : 3884 (72698 expanded)
%              Number of equality atoms :  224 (4949 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['15','18','21','22','23','24'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('30',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('32',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X11 @ X12 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('35',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X11 @ X12 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('51',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('52',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('53',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('54',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('55',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('56',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k6_partfun1 @ ( k2_relat_1 @ X2 ) ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['15','18','21','22','23','24'])).

thf('77',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k6_partfun1 @ ( k2_relat_1 @ X2 ) ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('78',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('80',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('83',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('93',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('94',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','95'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('97',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('98',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('99',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('101',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('103',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( zip_tseitin_0 @ X45 @ X48 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45 ) )
      | ( zip_tseitin_1 @ X47 @ X46 )
      | ( ( k2_relset_1 @ X49 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('109',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('110',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ ( k6_partfun1 @ ( k2_relat_1 @ X2 ) ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('114',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('115',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('116',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','116'])).

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

thf('118',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('119',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('120',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('123',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('126',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('127',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('128',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('130',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','124','125','128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['108','132','133','134','135','136'])).

thf('138',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('140',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('144',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['81','144'])).

thf('146',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('147',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X11 @ X12 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('148',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['15','18','21','22','23','24'])).

thf('150',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('151',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('154',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','156','157','160'])).

thf('162',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['142','143'])).

thf('164',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('166',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( X53 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X53 ) ) )
      | ( ( k5_relat_1 @ X54 @ ( k2_funct_1 @ X54 ) )
        = ( k6_partfun1 @ X55 ) )
      | ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X55 @ X53 @ X54 )
       != X53 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('167',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['15','18','21','22','23','24'])).

thf('170',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['167','170','171','172'])).

thf('174',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

thf('177',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['142','143'])).

thf('178',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('180',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('181',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('183',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('184',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('185',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['182','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['181','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['180','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['179','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['178','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['15','18','21','22','23','24'])).

thf('198',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('199',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('200',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('203',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('204',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('206',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['203','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['202','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['201','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['200','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['199','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['198','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['197','220'])).

thf('222',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['78','79'])).

thf('223',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('224',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['221','222','223','224'])).

thf('226',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['142','143'])).

thf('227',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('229',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['228','229'])).

thf('231',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ) ),
    inference('sup-',[status(thm)],['227','230'])).

thf('232',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['15','18','21','22','23','24'])).

thf('233',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('234',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('235',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('238',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('239',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('240',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('242',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['240','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['239','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['238','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['237','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['236','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['235','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['234','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['233','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['232','258'])).

thf('260',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['78','79'])).

thf('261',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('262',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['142','143'])).

thf('265',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
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

thf('267',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('268',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('272',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['268','269','270','271'])).

thf('273',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['15','18','21','22','23','24'])).

thf('274',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['142','143'])).

thf('277',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['142','143'])).

thf('279',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('281',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['15','18','21','22','23','24'])).

thf('282',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['78','79'])).

thf('283',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['231','265','277','278','279','280','281','282'])).

thf('284',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['142','143'])).

thf('285',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('287',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['195','196','283','284','285','286'])).

thf('288',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['164','287'])).

thf('289',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','289'])).

thf('291',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['290','291'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cW7vLAhckz
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.02/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.20  % Solved by: fo/fo7.sh
% 1.02/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.20  % done 998 iterations in 0.730s
% 1.02/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.20  % SZS output start Refutation
% 1.02/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.02/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.02/1.20  thf(sk_C_type, type, sk_C: $i).
% 1.02/1.20  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.02/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.02/1.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.02/1.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.02/1.20  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.02/1.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.02/1.20  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.02/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.20  thf(sk_D_type, type, sk_D: $i).
% 1.02/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.20  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.02/1.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.02/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.02/1.20  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.02/1.20  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.02/1.20  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.02/1.20  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.02/1.20  thf(t36_funct_2, conjecture,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.02/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.20       ( ![D:$i]:
% 1.02/1.20         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.02/1.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.02/1.20           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.02/1.20               ( r2_relset_1 @
% 1.02/1.20                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.02/1.20                 ( k6_partfun1 @ A ) ) & 
% 1.02/1.20               ( v2_funct_1 @ C ) ) =>
% 1.02/1.20             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.02/1.20               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.02/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.20    (~( ![A:$i,B:$i,C:$i]:
% 1.02/1.20        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.02/1.20            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.20          ( ![D:$i]:
% 1.02/1.20            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.02/1.20                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.02/1.20              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.02/1.20                  ( r2_relset_1 @
% 1.02/1.20                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.02/1.20                    ( k6_partfun1 @ A ) ) & 
% 1.02/1.20                  ( v2_funct_1 @ C ) ) =>
% 1.02/1.20                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.02/1.20                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.02/1.20    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.02/1.20  thf('0', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('1', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(redefinition_k1_partfun1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.02/1.20     ( ( ( v1_funct_1 @ E ) & 
% 1.02/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.02/1.20         ( v1_funct_1 @ F ) & 
% 1.02/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.02/1.20       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.02/1.20  thf('2', plain,
% 1.02/1.20      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.02/1.20         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.02/1.20          | ~ (v1_funct_1 @ X30)
% 1.02/1.20          | ~ (v1_funct_1 @ X33)
% 1.02/1.20          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.02/1.20          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 1.02/1.20              = (k5_relat_1 @ X30 @ X33)))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.02/1.20  thf('3', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.02/1.20            = (k5_relat_1 @ sk_C @ X0))
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['1', '2'])).
% 1.02/1.20  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('5', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.02/1.20            = (k5_relat_1 @ sk_C @ X0))
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.02/1.20          | ~ (v1_funct_1 @ X0))),
% 1.02/1.20      inference('demod', [status(thm)], ['3', '4'])).
% 1.02/1.20  thf('6', plain,
% 1.02/1.20      ((~ (v1_funct_1 @ sk_D)
% 1.02/1.20        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['0', '5'])).
% 1.02/1.20  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('8', plain,
% 1.02/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['6', '7'])).
% 1.02/1.20  thf('9', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(t24_funct_2, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.02/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.20       ( ![D:$i]:
% 1.02/1.20         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.02/1.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.02/1.20           ( ( r2_relset_1 @
% 1.02/1.20               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.02/1.20               ( k6_partfun1 @ B ) ) =>
% 1.02/1.20             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.02/1.20  thf('10', plain,
% 1.02/1.20      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.02/1.20         (~ (v1_funct_1 @ X37)
% 1.02/1.20          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.02/1.20          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.02/1.20          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 1.02/1.20               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 1.02/1.20               (k6_partfun1 @ X38))
% 1.02/1.20          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 1.02/1.20          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.02/1.20          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.02/1.20          | ~ (v1_funct_1 @ X40))),
% 1.02/1.20      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.02/1.20  thf('11', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.02/1.20          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.02/1.20          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.02/1.20               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.02/1.20               (k6_partfun1 @ sk_A))
% 1.02/1.20          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.02/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['9', '10'])).
% 1.02/1.20  thf('12', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('14', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.02/1.20          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.02/1.20          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.02/1.20               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.02/1.20               (k6_partfun1 @ sk_A)))),
% 1.02/1.20      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.02/1.20  thf('15', plain,
% 1.02/1.20      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.02/1.20           (k6_partfun1 @ sk_A))
% 1.02/1.20        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.02/1.20        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.02/1.20        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.02/1.20        | ~ (v1_funct_1 @ sk_D))),
% 1.02/1.20      inference('sup-', [status(thm)], ['8', '14'])).
% 1.02/1.20  thf('16', plain,
% 1.02/1.20      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.02/1.20        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.02/1.20        (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('17', plain,
% 1.02/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['6', '7'])).
% 1.02/1.20  thf('18', plain,
% 1.02/1.20      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.02/1.20        (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['16', '17'])).
% 1.02/1.20  thf('19', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(redefinition_k2_relset_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.02/1.20       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.02/1.20  thf('20', plain,
% 1.02/1.20      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.02/1.20         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.02/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.02/1.20  thf('21', plain,
% 1.02/1.20      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.02/1.20      inference('sup-', [status(thm)], ['19', '20'])).
% 1.02/1.20  thf('22', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('23', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('25', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['15', '18', '21', '22', '23', '24'])).
% 1.02/1.20  thf(t55_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.02/1.20       ( ( v2_funct_1 @ A ) =>
% 1.02/1.20         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.02/1.20           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.02/1.20  thf('26', plain,
% 1.02/1.20      (![X9 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X9)
% 1.02/1.20          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.02/1.20          | ~ (v1_funct_1 @ X9)
% 1.02/1.20          | ~ (v1_relat_1 @ X9))),
% 1.02/1.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.02/1.20  thf(dt_k2_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.02/1.20       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.02/1.20         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.02/1.20  thf('27', plain,
% 1.02/1.20      (![X3 : $i]:
% 1.02/1.20         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.20          | ~ (v1_funct_1 @ X3)
% 1.02/1.20          | ~ (v1_relat_1 @ X3))),
% 1.02/1.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.20  thf('28', plain,
% 1.02/1.20      (![X3 : $i]:
% 1.02/1.20         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.02/1.20          | ~ (v1_funct_1 @ X3)
% 1.02/1.20          | ~ (v1_relat_1 @ X3))),
% 1.02/1.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.20  thf(fc6_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 1.02/1.20       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.02/1.20         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 1.02/1.20         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.02/1.20  thf('29', plain,
% 1.02/1.20      (![X6 : $i]:
% 1.02/1.20         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 1.02/1.20          | ~ (v2_funct_1 @ X6)
% 1.02/1.20          | ~ (v1_funct_1 @ X6)
% 1.02/1.20          | ~ (v1_relat_1 @ X6))),
% 1.02/1.20      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.02/1.20  thf('30', plain,
% 1.02/1.20      (![X9 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X9)
% 1.02/1.20          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 1.02/1.20          | ~ (v1_funct_1 @ X9)
% 1.02/1.20          | ~ (v1_relat_1 @ X9))),
% 1.02/1.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.02/1.20  thf(t61_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.02/1.20       ( ( v2_funct_1 @ A ) =>
% 1.02/1.20         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.02/1.20             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.02/1.20           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.02/1.20             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.02/1.20  thf('31', plain,
% 1.02/1.20      (![X10 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X10)
% 1.02/1.20          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.02/1.20              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 1.02/1.20          | ~ (v1_funct_1 @ X10)
% 1.02/1.20          | ~ (v1_relat_1 @ X10))),
% 1.02/1.20      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.02/1.20  thf(redefinition_k6_partfun1, axiom,
% 1.02/1.20    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.02/1.20  thf('32', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('33', plain,
% 1.02/1.20      (![X10 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X10)
% 1.02/1.20          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.02/1.20              = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 1.02/1.20          | ~ (v1_funct_1 @ X10)
% 1.02/1.20          | ~ (v1_relat_1 @ X10))),
% 1.02/1.20      inference('demod', [status(thm)], ['31', '32'])).
% 1.02/1.20  thf(t64_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.02/1.20       ( ![B:$i]:
% 1.02/1.20         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.02/1.20           ( ( ( v2_funct_1 @ A ) & 
% 1.02/1.20               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.02/1.20               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.02/1.20             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.02/1.20  thf('34', plain,
% 1.02/1.20      (![X11 : $i, X12 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X11)
% 1.02/1.20          | ~ (v1_funct_1 @ X11)
% 1.02/1.20          | ((X11) = (k2_funct_1 @ X12))
% 1.02/1.20          | ((k5_relat_1 @ X11 @ X12) != (k6_relat_1 @ (k2_relat_1 @ X12)))
% 1.02/1.20          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 1.02/1.20          | ~ (v2_funct_1 @ X12)
% 1.02/1.20          | ~ (v1_funct_1 @ X12)
% 1.02/1.20          | ~ (v1_relat_1 @ X12))),
% 1.02/1.20      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.02/1.20  thf('35', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('36', plain,
% 1.02/1.20      (![X11 : $i, X12 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X11)
% 1.02/1.20          | ~ (v1_funct_1 @ X11)
% 1.02/1.20          | ((X11) = (k2_funct_1 @ X12))
% 1.02/1.20          | ((k5_relat_1 @ X11 @ X12) != (k6_partfun1 @ (k2_relat_1 @ X12)))
% 1.02/1.20          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 1.02/1.20          | ~ (v2_funct_1 @ X12)
% 1.02/1.20          | ~ (v1_funct_1 @ X12)
% 1.02/1.20          | ~ (v1_relat_1 @ X12))),
% 1.02/1.20      inference('demod', [status(thm)], ['34', '35'])).
% 1.02/1.20  thf('37', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.02/1.20            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('sup-', [status(thm)], ['33', '36'])).
% 1.02/1.20  thf('38', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.02/1.20              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.02/1.20      inference('simplify', [status(thm)], ['37'])).
% 1.02/1.20  thf('39', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.02/1.20            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['30', '38'])).
% 1.02/1.20  thf('40', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['39'])).
% 1.02/1.20  thf('41', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['29', '40'])).
% 1.02/1.20  thf('42', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['41'])).
% 1.02/1.20  thf('43', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['28', '42'])).
% 1.02/1.20  thf('44', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['43'])).
% 1.02/1.20  thf('45', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['27', '44'])).
% 1.02/1.20  thf('46', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['45'])).
% 1.02/1.20  thf('47', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['26', '46'])).
% 1.02/1.20  thf('48', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['47'])).
% 1.02/1.20  thf('49', plain,
% 1.02/1.20      (![X6 : $i]:
% 1.02/1.20         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 1.02/1.20          | ~ (v2_funct_1 @ X6)
% 1.02/1.20          | ~ (v1_funct_1 @ X6)
% 1.02/1.20          | ~ (v1_relat_1 @ X6))),
% 1.02/1.20      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.02/1.20  thf('50', plain,
% 1.02/1.20      (![X3 : $i]:
% 1.02/1.20         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.02/1.20          | ~ (v1_funct_1 @ X3)
% 1.02/1.20          | ~ (v1_relat_1 @ X3))),
% 1.02/1.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.20  thf('51', plain,
% 1.02/1.20      (![X3 : $i]:
% 1.02/1.20         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.20          | ~ (v1_funct_1 @ X3)
% 1.02/1.20          | ~ (v1_relat_1 @ X3))),
% 1.02/1.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.20  thf('52', plain,
% 1.02/1.20      (![X9 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X9)
% 1.02/1.20          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.02/1.20          | ~ (v1_funct_1 @ X9)
% 1.02/1.20          | ~ (v1_relat_1 @ X9))),
% 1.02/1.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.02/1.20  thf('53', plain,
% 1.02/1.20      (![X3 : $i]:
% 1.02/1.20         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.20          | ~ (v1_funct_1 @ X3)
% 1.02/1.20          | ~ (v1_relat_1 @ X3))),
% 1.02/1.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.20  thf('54', plain,
% 1.02/1.20      (![X9 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X9)
% 1.02/1.20          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 1.02/1.20          | ~ (v1_funct_1 @ X9)
% 1.02/1.20          | ~ (v1_relat_1 @ X9))),
% 1.02/1.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.02/1.20  thf(t80_relat_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( v1_relat_1 @ A ) =>
% 1.02/1.20       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.02/1.20  thf('55', plain,
% 1.02/1.20      (![X2 : $i]:
% 1.02/1.20         (((k5_relat_1 @ X2 @ (k6_relat_1 @ (k2_relat_1 @ X2))) = (X2))
% 1.02/1.20          | ~ (v1_relat_1 @ X2))),
% 1.02/1.20      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.02/1.20  thf('56', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('57', plain,
% 1.02/1.20      (![X2 : $i]:
% 1.02/1.20         (((k5_relat_1 @ X2 @ (k6_partfun1 @ (k2_relat_1 @ X2))) = (X2))
% 1.02/1.20          | ~ (v1_relat_1 @ X2))),
% 1.02/1.20      inference('demod', [status(thm)], ['55', '56'])).
% 1.02/1.20  thf('58', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.02/1.20            = (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.02/1.20      inference('sup+', [status(thm)], ['54', '57'])).
% 1.02/1.20  thf('59', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.02/1.20              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['53', '58'])).
% 1.02/1.20  thf('60', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.02/1.20            = (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['59'])).
% 1.02/1.20  thf('61', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.02/1.20            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.02/1.20      inference('sup+', [status(thm)], ['52', '60'])).
% 1.02/1.20  thf('62', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.02/1.20              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['51', '61'])).
% 1.02/1.20  thf('63', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.02/1.20            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['62'])).
% 1.02/1.20  thf('64', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.02/1.20              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['50', '63'])).
% 1.02/1.20  thf('65', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.02/1.20            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['64'])).
% 1.02/1.20  thf('66', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.02/1.20              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['49', '65'])).
% 1.02/1.20  thf('67', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.02/1.20            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['66'])).
% 1.02/1.20  thf('68', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v2_funct_1 @ X0))),
% 1.02/1.20      inference('sup+', [status(thm)], ['48', '67'])).
% 1.02/1.20  thf('69', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (v2_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_relat_1 @ X0)
% 1.02/1.20          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.20              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.20      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.20  thf('70', plain,
% 1.02/1.20      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A))
% 1.02/1.20          = (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 1.02/1.20        | ~ (v1_relat_1 @ sk_D)
% 1.02/1.20        | ~ (v1_funct_1 @ sk_D)
% 1.02/1.20        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.20      inference('sup+', [status(thm)], ['25', '69'])).
% 1.02/1.20  thf('71', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(cc1_relset_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.02/1.20       ( v1_relat_1 @ C ) ))).
% 1.02/1.20  thf('72', plain,
% 1.02/1.20      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.02/1.20         ((v1_relat_1 @ X13)
% 1.02/1.20          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.02/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.02/1.20  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.20      inference('sup-', [status(thm)], ['71', '72'])).
% 1.02/1.20  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('75', plain,
% 1.02/1.20      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A))
% 1.02/1.20          = (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 1.02/1.20        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['70', '73', '74'])).
% 1.02/1.20  thf('76', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['15', '18', '21', '22', '23', '24'])).
% 1.02/1.20  thf('77', plain,
% 1.02/1.20      (![X2 : $i]:
% 1.02/1.20         (((k5_relat_1 @ X2 @ (k6_partfun1 @ (k2_relat_1 @ X2))) = (X2))
% 1.02/1.20          | ~ (v1_relat_1 @ X2))),
% 1.02/1.20      inference('demod', [status(thm)], ['55', '56'])).
% 1.02/1.20  thf('78', plain,
% 1.02/1.20      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))
% 1.02/1.20        | ~ (v1_relat_1 @ sk_D))),
% 1.02/1.20      inference('sup+', [status(thm)], ['76', '77'])).
% 1.02/1.20  thf('79', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.20      inference('sup-', [status(thm)], ['71', '72'])).
% 1.02/1.20  thf('80', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['78', '79'])).
% 1.02/1.20  thf('81', plain,
% 1.02/1.20      ((((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))) | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['75', '80'])).
% 1.02/1.20  thf('82', plain,
% 1.02/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['6', '7'])).
% 1.02/1.20  thf('83', plain,
% 1.02/1.20      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.02/1.20        (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['16', '17'])).
% 1.02/1.20  thf('84', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('85', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(dt_k1_partfun1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.02/1.20     ( ( ( v1_funct_1 @ E ) & 
% 1.02/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.02/1.20         ( v1_funct_1 @ F ) & 
% 1.02/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.02/1.20       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.02/1.20         ( m1_subset_1 @
% 1.02/1.20           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.02/1.20           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.02/1.20  thf('86', plain,
% 1.02/1.20      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.02/1.20         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.02/1.20          | ~ (v1_funct_1 @ X24)
% 1.02/1.20          | ~ (v1_funct_1 @ X27)
% 1.02/1.20          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.02/1.20          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 1.02/1.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 1.02/1.20      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.02/1.20  thf('87', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.02/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.02/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.02/1.20          | ~ (v1_funct_1 @ X1)
% 1.02/1.20          | ~ (v1_funct_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['85', '86'])).
% 1.02/1.20  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('89', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.02/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.02/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.02/1.20          | ~ (v1_funct_1 @ X1))),
% 1.02/1.20      inference('demod', [status(thm)], ['87', '88'])).
% 1.02/1.20  thf('90', plain,
% 1.02/1.20      ((~ (v1_funct_1 @ sk_D)
% 1.02/1.20        | (m1_subset_1 @ 
% 1.02/1.20           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.02/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['84', '89'])).
% 1.02/1.20  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('92', plain,
% 1.02/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.02/1.20      inference('demod', [status(thm)], ['6', '7'])).
% 1.02/1.20  thf('93', plain,
% 1.02/1.20      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.02/1.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.02/1.20      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.02/1.20  thf(redefinition_r2_relset_1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.20     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.02/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.20       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.02/1.20  thf('94', plain,
% 1.02/1.20      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.02/1.20         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.02/1.20          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.02/1.20          | ((X19) = (X22))
% 1.02/1.20          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.02/1.20  thf('95', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.02/1.20          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['93', '94'])).
% 1.02/1.20  thf('96', plain,
% 1.02/1.20      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.02/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.02/1.20        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['83', '95'])).
% 1.02/1.20  thf(t29_relset_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( m1_subset_1 @
% 1.02/1.20       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.02/1.20  thf('97', plain,
% 1.02/1.20      (![X23 : $i]:
% 1.02/1.20         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 1.02/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.02/1.20      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.02/1.20  thf('98', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('99', plain,
% 1.02/1.20      (![X23 : $i]:
% 1.02/1.20         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 1.02/1.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.02/1.20      inference('demod', [status(thm)], ['97', '98'])).
% 1.02/1.20  thf('100', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['96', '99'])).
% 1.02/1.20  thf('101', plain,
% 1.02/1.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.02/1.20         = (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['82', '100'])).
% 1.02/1.20  thf('102', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf(t30_funct_2, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.20     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.02/1.20         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.02/1.20       ( ![E:$i]:
% 1.02/1.20         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.02/1.20             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.02/1.20           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.02/1.20               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.02/1.20             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.02/1.20               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.02/1.20  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.02/1.20  thf(zf_stmt_2, axiom,
% 1.02/1.20    (![C:$i,B:$i]:
% 1.02/1.20     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.02/1.20       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.02/1.20  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.02/1.20  thf(zf_stmt_4, axiom,
% 1.02/1.20    (![E:$i,D:$i]:
% 1.02/1.20     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.02/1.20  thf(zf_stmt_5, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.20     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.02/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.20       ( ![E:$i]:
% 1.02/1.20         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.02/1.20             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.02/1.20           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.02/1.20               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.02/1.20             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.02/1.20  thf('103', plain,
% 1.02/1.20      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.02/1.20         (~ (v1_funct_1 @ X45)
% 1.02/1.20          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 1.02/1.20          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.02/1.20          | (zip_tseitin_0 @ X45 @ X48)
% 1.02/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 1.02/1.20          | (zip_tseitin_1 @ X47 @ X46)
% 1.02/1.20          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 1.02/1.20          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 1.02/1.20          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 1.02/1.20          | ~ (v1_funct_1 @ X48))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.02/1.20  thf('104', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.02/1.20          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.02/1.20          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.02/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.02/1.20          | (zip_tseitin_0 @ sk_D @ X0)
% 1.02/1.20          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.02/1.20          | ~ (v1_funct_1 @ sk_D))),
% 1.02/1.20      inference('sup-', [status(thm)], ['102', '103'])).
% 1.02/1.20  thf('105', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('107', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (v1_funct_1 @ X0)
% 1.02/1.20          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.02/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.02/1.20          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.02/1.20          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.02/1.20          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.02/1.20          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.02/1.20      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.02/1.20  thf('108', plain,
% 1.02/1.20      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.02/1.20        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.02/1.20        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.02/1.20        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.02/1.20        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.02/1.20        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.02/1.20        | ~ (v1_funct_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['101', '107'])).
% 1.02/1.20  thf(t71_relat_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.02/1.20       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.02/1.20  thf('109', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 1.02/1.20      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.02/1.20  thf('110', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('111', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X1)) = (X1))),
% 1.02/1.20      inference('demod', [status(thm)], ['109', '110'])).
% 1.02/1.20  thf('112', plain,
% 1.02/1.20      (![X2 : $i]:
% 1.02/1.20         (((k5_relat_1 @ X2 @ (k6_partfun1 @ (k2_relat_1 @ X2))) = (X2))
% 1.02/1.20          | ~ (v1_relat_1 @ X2))),
% 1.02/1.20      inference('demod', [status(thm)], ['55', '56'])).
% 1.02/1.20  thf('113', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.02/1.20            = (k6_partfun1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.02/1.20      inference('sup+', [status(thm)], ['111', '112'])).
% 1.02/1.20  thf(fc3_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.02/1.20       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.02/1.20  thf('114', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 1.02/1.20      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.02/1.20  thf('115', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('116', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 1.02/1.20      inference('demod', [status(thm)], ['114', '115'])).
% 1.02/1.20  thf('117', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.02/1.20           = (k6_partfun1 @ X0))),
% 1.02/1.20      inference('demod', [status(thm)], ['113', '116'])).
% 1.02/1.20  thf(t53_funct_1, axiom,
% 1.02/1.20    (![A:$i]:
% 1.02/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.02/1.20       ( ( ?[B:$i]:
% 1.02/1.20           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.02/1.20             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 1.02/1.20         ( v2_funct_1 @ A ) ) ))).
% 1.02/1.20  thf('118', plain,
% 1.02/1.20      (![X7 : $i, X8 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X7)
% 1.02/1.20          | ~ (v1_funct_1 @ X7)
% 1.02/1.20          | ((k5_relat_1 @ X8 @ X7) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 1.02/1.20          | (v2_funct_1 @ X8)
% 1.02/1.20          | ~ (v1_funct_1 @ X8)
% 1.02/1.20          | ~ (v1_relat_1 @ X8))),
% 1.02/1.20      inference('cnf', [status(esa)], [t53_funct_1])).
% 1.02/1.20  thf('119', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('120', plain,
% 1.02/1.20      (![X7 : $i, X8 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X7)
% 1.02/1.20          | ~ (v1_funct_1 @ X7)
% 1.02/1.20          | ((k5_relat_1 @ X8 @ X7) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.02/1.20          | (v2_funct_1 @ X8)
% 1.02/1.20          | ~ (v1_funct_1 @ X8)
% 1.02/1.20          | ~ (v1_relat_1 @ X8))),
% 1.02/1.20      inference('demod', [status(thm)], ['118', '119'])).
% 1.02/1.20  thf('121', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k6_partfun1 @ X0)
% 1.02/1.20            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 1.02/1.20          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.02/1.20          | (v2_funct_1 @ (k6_partfun1 @ X0))
% 1.02/1.20          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.02/1.20          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['117', '120'])).
% 1.02/1.20  thf('122', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 1.02/1.20      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.02/1.20  thf('123', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('124', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.02/1.20      inference('demod', [status(thm)], ['122', '123'])).
% 1.02/1.20  thf('125', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 1.02/1.20      inference('demod', [status(thm)], ['114', '115'])).
% 1.02/1.20  thf('126', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 1.02/1.20      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.02/1.20  thf('127', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.20  thf('128', plain, (![X5 : $i]: (v1_funct_1 @ (k6_partfun1 @ X5))),
% 1.02/1.20      inference('demod', [status(thm)], ['126', '127'])).
% 1.02/1.20  thf('129', plain, (![X5 : $i]: (v1_funct_1 @ (k6_partfun1 @ X5))),
% 1.02/1.20      inference('demod', [status(thm)], ['126', '127'])).
% 1.02/1.20  thf('130', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 1.02/1.20      inference('demod', [status(thm)], ['114', '115'])).
% 1.02/1.20  thf('131', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 1.02/1.20          | (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 1.02/1.20      inference('demod', [status(thm)],
% 1.02/1.20                ['121', '124', '125', '128', '129', '130'])).
% 1.02/1.20  thf('132', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 1.02/1.20      inference('simplify', [status(thm)], ['131'])).
% 1.02/1.20  thf('133', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('134', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('135', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('137', plain,
% 1.02/1.20      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.02/1.20        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.02/1.20        | ((sk_B) != (sk_B)))),
% 1.02/1.20      inference('demod', [status(thm)],
% 1.02/1.20                ['108', '132', '133', '134', '135', '136'])).
% 1.02/1.20  thf('138', plain,
% 1.02/1.20      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.02/1.20      inference('simplify', [status(thm)], ['137'])).
% 1.02/1.20  thf('139', plain,
% 1.02/1.20      (![X43 : $i, X44 : $i]:
% 1.02/1.20         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.20  thf('140', plain,
% 1.02/1.20      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['138', '139'])).
% 1.02/1.20  thf('141', plain, (((sk_A) != (k1_xboole_0))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('142', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.02/1.20      inference('simplify_reflect-', [status(thm)], ['140', '141'])).
% 1.02/1.20  thf('143', plain,
% 1.02/1.20      (![X41 : $i, X42 : $i]:
% 1.02/1.20         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.02/1.20  thf('144', plain, ((v2_funct_1 @ sk_D)),
% 1.02/1.20      inference('sup-', [status(thm)], ['142', '143'])).
% 1.02/1.20  thf('145', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 1.02/1.20      inference('demod', [status(thm)], ['81', '144'])).
% 1.02/1.20  thf('146', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['96', '99'])).
% 1.02/1.20  thf('147', plain,
% 1.02/1.20      (![X11 : $i, X12 : $i]:
% 1.02/1.20         (~ (v1_relat_1 @ X11)
% 1.02/1.20          | ~ (v1_funct_1 @ X11)
% 1.02/1.20          | ((X11) = (k2_funct_1 @ X12))
% 1.02/1.20          | ((k5_relat_1 @ X11 @ X12) != (k6_partfun1 @ (k2_relat_1 @ X12)))
% 1.02/1.20          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 1.02/1.20          | ~ (v2_funct_1 @ X12)
% 1.02/1.20          | ~ (v1_funct_1 @ X12)
% 1.02/1.20          | ~ (v1_relat_1 @ X12))),
% 1.02/1.20      inference('demod', [status(thm)], ['34', '35'])).
% 1.02/1.20  thf('148', plain,
% 1.02/1.20      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.02/1.20        | ~ (v1_relat_1 @ sk_D)
% 1.02/1.20        | ~ (v1_funct_1 @ sk_D)
% 1.02/1.20        | ~ (v2_funct_1 @ sk_D)
% 1.02/1.20        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.02/1.20        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.02/1.20        | ~ (v1_funct_1 @ sk_C)
% 1.02/1.20        | ~ (v1_relat_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['146', '147'])).
% 1.02/1.20  thf('149', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.02/1.20      inference('demod', [status(thm)], ['15', '18', '21', '22', '23', '24'])).
% 1.02/1.20  thf('150', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.20      inference('sup-', [status(thm)], ['71', '72'])).
% 1.02/1.20  thf('151', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('152', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('153', plain,
% 1.02/1.20      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.02/1.20         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.02/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.02/1.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.02/1.20  thf('154', plain,
% 1.02/1.20      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.02/1.20      inference('sup-', [status(thm)], ['152', '153'])).
% 1.02/1.20  thf('155', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('156', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.02/1.20      inference('sup+', [status(thm)], ['154', '155'])).
% 1.02/1.20  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('158', plain,
% 1.02/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('159', plain,
% 1.02/1.20      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.02/1.20         ((v1_relat_1 @ X13)
% 1.02/1.20          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.02/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.02/1.20  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.20      inference('sup-', [status(thm)], ['158', '159'])).
% 1.02/1.20  thf('161', plain,
% 1.02/1.20      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.02/1.20        | ~ (v2_funct_1 @ sk_D)
% 1.02/1.20        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.02/1.20        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.02/1.20      inference('demod', [status(thm)],
% 1.02/1.20                ['148', '149', '150', '151', '156', '157', '160'])).
% 1.02/1.20  thf('162', plain,
% 1.02/1.20      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.02/1.21        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('simplify', [status(thm)], ['161'])).
% 1.02/1.21  thf('163', plain, ((v2_funct_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['142', '143'])).
% 1.02/1.21  thf('164', plain,
% 1.02/1.21      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.02/1.21      inference('demod', [status(thm)], ['162', '163'])).
% 1.02/1.21  thf('165', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(t35_funct_2, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i]:
% 1.02/1.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.02/1.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.21       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.02/1.21         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.02/1.21           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.02/1.21             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.02/1.21  thf('166', plain,
% 1.02/1.21      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.02/1.21         (((X53) = (k1_xboole_0))
% 1.02/1.21          | ~ (v1_funct_1 @ X54)
% 1.02/1.21          | ~ (v1_funct_2 @ X54 @ X55 @ X53)
% 1.02/1.21          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X53)))
% 1.02/1.21          | ((k5_relat_1 @ X54 @ (k2_funct_1 @ X54)) = (k6_partfun1 @ X55))
% 1.02/1.21          | ~ (v2_funct_1 @ X54)
% 1.02/1.21          | ((k2_relset_1 @ X55 @ X53 @ X54) != (X53)))),
% 1.02/1.21      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.02/1.21  thf('167', plain,
% 1.02/1.21      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D)
% 1.02/1.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.02/1.21        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.02/1.21        | ~ (v1_funct_1 @ sk_D)
% 1.02/1.21        | ((sk_A) = (k1_xboole_0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['165', '166'])).
% 1.02/1.21  thf('168', plain,
% 1.02/1.21      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.02/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.02/1.21  thf('169', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['15', '18', '21', '22', '23', '24'])).
% 1.02/1.21  thf('170', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['168', '169'])).
% 1.02/1.21  thf('171', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('172', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('173', plain,
% 1.02/1.21      ((((sk_A) != (sk_A))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D)
% 1.02/1.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.02/1.21        | ((sk_A) = (k1_xboole_0)))),
% 1.02/1.21      inference('demod', [status(thm)], ['167', '170', '171', '172'])).
% 1.02/1.21  thf('174', plain,
% 1.02/1.21      ((((sk_A) = (k1_xboole_0))
% 1.02/1.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('simplify', [status(thm)], ['173'])).
% 1.02/1.21  thf('175', plain, (((sk_A) != (k1_xboole_0))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('176', plain,
% 1.02/1.21      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 1.02/1.21  thf('177', plain, ((v2_funct_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['142', '143'])).
% 1.02/1.21  thf('178', plain,
% 1.02/1.21      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.02/1.21      inference('demod', [status(thm)], ['176', '177'])).
% 1.02/1.21  thf('179', plain,
% 1.02/1.21      (![X6 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 1.02/1.21          | ~ (v2_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_relat_1 @ X6))),
% 1.02/1.21      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.02/1.21  thf('180', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('181', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('182', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['47'])).
% 1.02/1.21  thf('183', plain,
% 1.02/1.21      (![X10 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X10)
% 1.02/1.21          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 1.02/1.21              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.02/1.21          | ~ (v1_funct_1 @ X10)
% 1.02/1.21          | ~ (v1_relat_1 @ X10))),
% 1.02/1.21      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.02/1.21  thf('184', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.02/1.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.02/1.21  thf('185', plain,
% 1.02/1.21      (![X10 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X10)
% 1.02/1.21          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 1.02/1.21              = (k6_partfun1 @ (k2_relat_1 @ X10)))
% 1.02/1.21          | ~ (v1_funct_1 @ X10)
% 1.02/1.21          | ~ (v1_relat_1 @ X10))),
% 1.02/1.21      inference('demod', [status(thm)], ['183', '184'])).
% 1.02/1.21  thf('186', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.02/1.21            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['182', '185'])).
% 1.02/1.21  thf('187', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.02/1.21              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['181', '186'])).
% 1.02/1.21  thf('188', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.02/1.21            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['187'])).
% 1.02/1.21  thf('189', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.02/1.21              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['180', '188'])).
% 1.02/1.21  thf('190', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.02/1.21            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['189'])).
% 1.02/1.21  thf('191', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.02/1.21              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['179', '190'])).
% 1.02/1.21  thf('192', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.02/1.21            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['191'])).
% 1.02/1.21  thf('193', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.02/1.21      inference('demod', [status(thm)], ['122', '123'])).
% 1.02/1.21  thf('194', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 1.02/1.21            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['192', '193'])).
% 1.02/1.21  thf('195', plain,
% 1.02/1.21      ((((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.02/1.21          = (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D)
% 1.02/1.21        | ~ (v1_funct_1 @ sk_D)
% 1.02/1.21        | ~ (v1_relat_1 @ sk_D))),
% 1.02/1.21      inference('sup+', [status(thm)], ['178', '194'])).
% 1.02/1.21  thf('196', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.02/1.21      inference('demod', [status(thm)], ['122', '123'])).
% 1.02/1.21  thf('197', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['15', '18', '21', '22', '23', '24'])).
% 1.02/1.21  thf('198', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('199', plain,
% 1.02/1.21      (![X6 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 1.02/1.21          | ~ (v2_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_relat_1 @ X6))),
% 1.02/1.21      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.02/1.21  thf('200', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('201', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.21              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.21  thf('202', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.21              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.21  thf('203', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('204', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('205', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.21              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.21  thf('206', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('207', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['205', '206'])).
% 1.02/1.21  thf('208', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['204', '207'])).
% 1.02/1.21  thf('209', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['208'])).
% 1.02/1.21  thf('210', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['203', '209'])).
% 1.02/1.21  thf('211', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['210'])).
% 1.02/1.21  thf('212', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['202', '211'])).
% 1.02/1.21  thf('213', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['212'])).
% 1.02/1.21  thf('214', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_relat_1 @ 
% 1.02/1.21           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['201', '213'])).
% 1.02/1.21  thf('215', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | (v1_relat_1 @ 
% 1.02/1.21             (k2_funct_1 @ 
% 1.02/1.21              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['200', '214'])).
% 1.02/1.21  thf('216', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_relat_1 @ 
% 1.02/1.21           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['215'])).
% 1.02/1.21  thf('217', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | (v1_relat_1 @ 
% 1.02/1.21             (k2_funct_1 @ 
% 1.02/1.21              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['199', '216'])).
% 1.02/1.21  thf('218', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_relat_1 @ 
% 1.02/1.21           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['217'])).
% 1.02/1.21  thf('219', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | (v1_relat_1 @ 
% 1.02/1.21             (k2_funct_1 @ 
% 1.02/1.21              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['198', '218'])).
% 1.02/1.21  thf('220', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_relat_1 @ 
% 1.02/1.21           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['219'])).
% 1.02/1.21  thf('221', plain,
% 1.02/1.21      (((v1_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A))))
% 1.02/1.21        | ~ (v1_relat_1 @ sk_D)
% 1.02/1.21        | ~ (v1_funct_1 @ sk_D)
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('sup+', [status(thm)], ['197', '220'])).
% 1.02/1.21  thf('222', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['78', '79'])).
% 1.02/1.21  thf('223', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['71', '72'])).
% 1.02/1.21  thf('224', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('225', plain,
% 1.02/1.21      (((v1_relat_1 @ (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['221', '222', '223', '224'])).
% 1.02/1.21  thf('226', plain, ((v2_funct_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['142', '143'])).
% 1.02/1.21  thf('227', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['225', '226'])).
% 1.02/1.21  thf('228', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.21              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.21  thf('229', plain,
% 1.02/1.21      (![X9 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X9)
% 1.02/1.21          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.02/1.21          | ~ (v1_funct_1 @ X9)
% 1.02/1.21          | ~ (v1_relat_1 @ X9))),
% 1.02/1.21      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.02/1.21  thf('230', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((k2_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21            = (k1_relat_1 @ 
% 1.02/1.21               (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['228', '229'])).
% 1.02/1.21  thf('231', plain,
% 1.02/1.21      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 1.02/1.21        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D)
% 1.02/1.21        | ~ (v1_funct_1 @ sk_D)
% 1.02/1.21        | ~ (v1_relat_1 @ sk_D)
% 1.02/1.21        | ((k2_relat_1 @ (k2_funct_1 @ sk_D))
% 1.02/1.21            = (k1_relat_1 @ 
% 1.02/1.21               (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['227', '230'])).
% 1.02/1.21  thf('232', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['15', '18', '21', '22', '23', '24'])).
% 1.02/1.21  thf('233', plain,
% 1.02/1.21      (![X6 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 1.02/1.21          | ~ (v2_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_relat_1 @ X6))),
% 1.02/1.21      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.02/1.21  thf('234', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('235', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('236', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.21              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.21  thf('237', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.21              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.21  thf('238', plain,
% 1.02/1.21      (![X6 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 1.02/1.21          | ~ (v2_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_relat_1 @ X6))),
% 1.02/1.21      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.02/1.21  thf('239', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_funct_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('240', plain,
% 1.02/1.21      (![X3 : $i]:
% 1.02/1.21         ((v1_relat_1 @ (k2_funct_1 @ X3))
% 1.02/1.21          | ~ (v1_funct_1 @ X3)
% 1.02/1.21          | ~ (v1_relat_1 @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.02/1.21  thf('241', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.02/1.21              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.21  thf('242', plain,
% 1.02/1.21      (![X6 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 1.02/1.21          | ~ (v2_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_funct_1 @ X6)
% 1.02/1.21          | ~ (v1_relat_1 @ X6))),
% 1.02/1.21      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.02/1.21  thf('243', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['241', '242'])).
% 1.02/1.21  thf('244', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | (v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['240', '243'])).
% 1.02/1.21  thf('245', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['244'])).
% 1.02/1.21  thf('246', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | (v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['239', '245'])).
% 1.02/1.21  thf('247', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['246'])).
% 1.02/1.21  thf('248', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | (v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['238', '247'])).
% 1.02/1.21  thf('249', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['248'])).
% 1.02/1.21  thf('250', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['237', '249'])).
% 1.02/1.21  thf('251', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['250'])).
% 1.02/1.21  thf('252', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ 
% 1.02/1.21           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['236', '251'])).
% 1.02/1.21  thf('253', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | (v2_funct_1 @ 
% 1.02/1.21             (k2_funct_1 @ 
% 1.02/1.21              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['235', '252'])).
% 1.02/1.21  thf('254', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ 
% 1.02/1.21           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['253'])).
% 1.02/1.21  thf('255', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | (v2_funct_1 @ 
% 1.02/1.21             (k2_funct_1 @ 
% 1.02/1.21              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['234', '254'])).
% 1.02/1.21  thf('256', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ 
% 1.02/1.21           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['255'])).
% 1.02/1.21  thf('257', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | (v2_funct_1 @ 
% 1.02/1.21             (k2_funct_1 @ 
% 1.02/1.21              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['233', '256'])).
% 1.02/1.21  thf('258', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_funct_1 @ 
% 1.02/1.21           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.02/1.21          | ~ (v2_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_funct_1 @ X0)
% 1.02/1.21          | ~ (v1_relat_1 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['257'])).
% 1.02/1.21  thf('259', plain,
% 1.02/1.21      (((v2_funct_1 @ (k2_funct_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A))))
% 1.02/1.21        | ~ (v1_relat_1 @ sk_D)
% 1.02/1.21        | ~ (v1_funct_1 @ sk_D)
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('sup+', [status(thm)], ['232', '258'])).
% 1.02/1.21  thf('260', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['78', '79'])).
% 1.02/1.21  thf('261', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['71', '72'])).
% 1.02/1.21  thf('262', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('263', plain,
% 1.02/1.21      (((v2_funct_1 @ (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 1.02/1.21  thf('264', plain, ((v2_funct_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['142', '143'])).
% 1.02/1.21  thf('265', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['263', '264'])).
% 1.02/1.21  thf('266', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(t31_funct_2, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i]:
% 1.02/1.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.02/1.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.02/1.21       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.02/1.21         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.02/1.21           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.02/1.21           ( m1_subset_1 @
% 1.02/1.21             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.02/1.21  thf('267', plain,
% 1.02/1.21      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.02/1.21         (~ (v2_funct_1 @ X50)
% 1.02/1.21          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 1.02/1.21          | (v1_funct_1 @ (k2_funct_1 @ X50))
% 1.02/1.21          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 1.02/1.21          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 1.02/1.21          | ~ (v1_funct_1 @ X50))),
% 1.02/1.21      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.02/1.21  thf('268', plain,
% 1.02/1.21      ((~ (v1_funct_1 @ sk_D)
% 1.02/1.21        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.02/1.21        | (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.02/1.21        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('sup-', [status(thm)], ['266', '267'])).
% 1.02/1.21  thf('269', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('270', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('271', plain,
% 1.02/1.21      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.02/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.02/1.21  thf('272', plain,
% 1.02/1.21      (((v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.02/1.21        | ((k2_relat_1 @ sk_D) != (sk_A))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['268', '269', '270', '271'])).
% 1.02/1.21  thf('273', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['15', '18', '21', '22', '23', '24'])).
% 1.02/1.21  thf('274', plain,
% 1.02/1.21      (((v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.02/1.21        | ((sk_A) != (sk_A))
% 1.02/1.21        | ~ (v2_funct_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['272', '273'])).
% 1.02/1.21  thf('275', plain,
% 1.02/1.21      ((~ (v2_funct_1 @ sk_D) | (v1_funct_1 @ (k2_funct_1 @ sk_D)))),
% 1.02/1.21      inference('simplify', [status(thm)], ['274'])).
% 1.02/1.21  thf('276', plain, ((v2_funct_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['142', '143'])).
% 1.02/1.21  thf('277', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['275', '276'])).
% 1.02/1.21  thf('278', plain, ((v2_funct_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['142', '143'])).
% 1.02/1.21  thf('279', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('280', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['71', '72'])).
% 1.02/1.21  thf('281', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['15', '18', '21', '22', '23', '24'])).
% 1.02/1.21  thf('282', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.02/1.21      inference('demod', [status(thm)], ['78', '79'])).
% 1.02/1.21  thf('283', plain,
% 1.02/1.21      (((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (k1_relat_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)],
% 1.02/1.21                ['231', '265', '277', '278', '279', '280', '281', '282'])).
% 1.02/1.21  thf('284', plain, ((v2_funct_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['142', '143'])).
% 1.02/1.21  thf('285', plain, ((v1_funct_1 @ sk_D)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('286', plain, ((v1_relat_1 @ sk_D)),
% 1.02/1.21      inference('sup-', [status(thm)], ['71', '72'])).
% 1.02/1.21  thf('287', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.02/1.21      inference('demod', [status(thm)],
% 1.02/1.21                ['195', '196', '283', '284', '285', '286'])).
% 1.02/1.21  thf('288', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.02/1.21      inference('demod', [status(thm)], ['164', '287'])).
% 1.02/1.21  thf('289', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.02/1.21      inference('simplify', [status(thm)], ['288'])).
% 1.02/1.21  thf('290', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.02/1.21      inference('demod', [status(thm)], ['145', '289'])).
% 1.02/1.21  thf('291', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('292', plain, ($false),
% 1.02/1.21      inference('simplify_reflect-', [status(thm)], ['290', '291'])).
% 1.02/1.21  
% 1.02/1.21  % SZS output end Refutation
% 1.02/1.21  
% 1.02/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
