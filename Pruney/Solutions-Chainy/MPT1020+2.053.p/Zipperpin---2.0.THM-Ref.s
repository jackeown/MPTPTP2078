%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Irhxjns3MW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:09 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 217 expanded)
%              Number of leaves         :   40 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          : 1173 (4764 expanded)
%              Number of equality atoms :   48 (  52 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_funct_2 @ X36 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('32',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('33',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16','35'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X5 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('38',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k2_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X38 @ X39 )
        = X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v3_funct_2 @ X16 @ X17 @ X18 )
      | ( v2_funct_2 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('62',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_2 @ X20 @ X19 )
      | ( ( k2_relat_1 @ X20 )
        = X19 )
      | ~ ( v5_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X38 @ X39 )
        = X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('80',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['75','76','77','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_A != sk_A )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','47','52','53','59','72','81','82','87'])).

thf('89',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 )
      | ( X12 != X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['8','89','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Irhxjns3MW
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.63  % Solved by: fo/fo7.sh
% 0.40/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.63  % done 336 iterations in 0.186s
% 0.40/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.63  % SZS output start Refutation
% 0.40/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.40/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.63  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.40/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.63  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.40/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.63  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.40/0.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.40/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.63  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.40/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.63  thf(t87_funct_2, conjecture,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.40/0.63         ( v3_funct_2 @ B @ A @ A ) & 
% 0.40/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.40/0.63       ( ![C:$i]:
% 0.40/0.63         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.40/0.63             ( v3_funct_2 @ C @ A @ A ) & 
% 0.40/0.63             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.40/0.63           ( ( r2_relset_1 @
% 0.40/0.63               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.40/0.63               ( k6_partfun1 @ A ) ) =>
% 0.40/0.63             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.40/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.63    (~( ![A:$i,B:$i]:
% 0.40/0.63        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.40/0.63            ( v3_funct_2 @ B @ A @ A ) & 
% 0.40/0.63            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.40/0.63          ( ![C:$i]:
% 0.40/0.63            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.40/0.63                ( v3_funct_2 @ C @ A @ A ) & 
% 0.40/0.63                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.40/0.63              ( ( r2_relset_1 @
% 0.40/0.63                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.40/0.63                  ( k6_partfun1 @ A ) ) =>
% 0.40/0.63                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.40/0.63    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.40/0.63  thf('0', plain,
% 0.40/0.63      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('1', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k2_funct_2, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.40/0.63         ( v3_funct_2 @ B @ A @ A ) & 
% 0.40/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.40/0.63       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.40/0.63  thf('2', plain,
% 0.40/0.63      (![X35 : $i, X36 : $i]:
% 0.40/0.63         (((k2_funct_2 @ X36 @ X35) = (k2_funct_1 @ X35))
% 0.40/0.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 0.40/0.63          | ~ (v3_funct_2 @ X35 @ X36 @ X36)
% 0.40/0.63          | ~ (v1_funct_2 @ X35 @ X36 @ X36)
% 0.40/0.63          | ~ (v1_funct_1 @ X35))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.40/0.63  thf('3', plain,
% 0.40/0.63      ((~ (v1_funct_1 @ sk_B)
% 0.40/0.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.40/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.40/0.63        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.63  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.40/0.63  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['0', '7'])).
% 0.40/0.63  thf('9', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('10', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k1_partfun1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.63     ( ( ( v1_funct_1 @ E ) & 
% 0.40/0.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.63         ( v1_funct_1 @ F ) & 
% 0.40/0.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.40/0.63       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.40/0.63  thf('11', plain,
% 0.40/0.63      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.40/0.63          | ~ (v1_funct_1 @ X29)
% 0.40/0.63          | ~ (v1_funct_1 @ X32)
% 0.40/0.63          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.40/0.63          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.40/0.63              = (k5_relat_1 @ X29 @ X32)))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.40/0.63  thf('12', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.40/0.63            = (k5_relat_1 @ sk_B @ X0))
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.40/0.63          | ~ (v1_funct_1 @ X0)
% 0.40/0.63          | ~ (v1_funct_1 @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.63  thf('13', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('14', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.40/0.63            = (k5_relat_1 @ sk_B @ X0))
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.40/0.63          | ~ (v1_funct_1 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.63  thf('15', plain,
% 0.40/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.63        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.40/0.63            = (k5_relat_1 @ sk_B @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['9', '14'])).
% 0.40/0.63  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('17', plain,
% 0.40/0.63      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.63        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.63        (k6_partfun1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k6_partfun1, axiom,
% 0.40/0.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.40/0.63  thf('18', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.40/0.63  thf('19', plain,
% 0.40/0.63      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.63        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.63        (k6_relat_1 @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.63  thf('20', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('21', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(dt_k1_partfun1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.63     ( ( ( v1_funct_1 @ E ) & 
% 0.40/0.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.63         ( v1_funct_1 @ F ) & 
% 0.40/0.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.40/0.63       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.40/0.63         ( m1_subset_1 @
% 0.40/0.63           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.40/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.40/0.63  thf('22', plain,
% 0.40/0.63      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.40/0.63          | ~ (v1_funct_1 @ X21)
% 0.40/0.63          | ~ (v1_funct_1 @ X24)
% 0.40/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.40/0.63          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 0.40/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.40/0.63  thf('23', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.40/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.40/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.40/0.63          | ~ (v1_funct_1 @ X1)
% 0.40/0.63          | ~ (v1_funct_1 @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.63  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('25', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.40/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.40/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.40/0.63          | ~ (v1_funct_1 @ X1))),
% 0.40/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.63  thf('26', plain,
% 0.40/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.63        | (m1_subset_1 @ 
% 0.40/0.63           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['20', '25'])).
% 0.40/0.63  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('28', plain,
% 0.40/0.63      ((m1_subset_1 @ 
% 0.40/0.63        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.40/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.63  thf(redefinition_r2_relset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.63     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.63       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.40/0.63  thf('29', plain,
% 0.40/0.63      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.63          | ((X12) = (X15))
% 0.40/0.63          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.40/0.63  thf('30', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.63             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.40/0.63          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.63  thf('31', plain,
% 0.40/0.63      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.40/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.40/0.63        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.40/0.63            = (k6_relat_1 @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['19', '30'])).
% 0.40/0.63  thf(dt_k6_partfun1, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( m1_subset_1 @
% 0.40/0.63         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.40/0.63       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.40/0.63  thf('32', plain,
% 0.40/0.63      (![X28 : $i]:
% 0.40/0.63         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 0.40/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.40/0.63  thf('33', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.40/0.63  thf('34', plain,
% 0.40/0.63      (![X28 : $i]:
% 0.40/0.63         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.40/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.40/0.63      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.63  thf('35', plain,
% 0.40/0.63      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.40/0.63         = (k6_relat_1 @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['31', '34'])).
% 0.40/0.63  thf('36', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ sk_C))),
% 0.40/0.63      inference('demod', [status(thm)], ['15', '16', '35'])).
% 0.40/0.63  thf(t63_funct_1, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.63           ( ( ( v2_funct_1 @ A ) & 
% 0.40/0.63               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.40/0.63               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.40/0.63             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.40/0.63  thf('37', plain,
% 0.40/0.63      (![X4 : $i, X5 : $i]:
% 0.40/0.63         (~ (v1_relat_1 @ X4)
% 0.40/0.63          | ~ (v1_funct_1 @ X4)
% 0.40/0.63          | ((X4) = (k2_funct_1 @ X5))
% 0.40/0.63          | ((k5_relat_1 @ X5 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.40/0.63          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.40/0.63          | ~ (v2_funct_1 @ X5)
% 0.40/0.63          | ~ (v1_funct_1 @ X5)
% 0.40/0.63          | ~ (v1_relat_1 @ X5))),
% 0.40/0.63      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.40/0.63  thf('38', plain,
% 0.40/0.63      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.40/0.63        | ~ (v1_relat_1 @ sk_B)
% 0.40/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.40/0.63        | ~ (v2_funct_1 @ sk_B)
% 0.40/0.63        | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ sk_C))
% 0.40/0.63        | ((sk_C) = (k2_funct_1 @ sk_B))
% 0.40/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.63        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.63  thf('39', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(t67_funct_2, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.40/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.40/0.63       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.40/0.63  thf('40', plain,
% 0.40/0.63      (![X38 : $i, X39 : $i]:
% 0.40/0.63         (((k1_relset_1 @ X38 @ X38 @ X39) = (X38))
% 0.40/0.63          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.40/0.63          | ~ (v1_funct_2 @ X39 @ X38 @ X38)
% 0.40/0.63          | ~ (v1_funct_1 @ X39))),
% 0.40/0.63      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.40/0.63  thf('41', plain,
% 0.40/0.63      ((~ (v1_funct_1 @ sk_B)
% 0.40/0.63        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.40/0.63        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.63  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('43', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('44', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.63  thf('45', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.63         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.40/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.63  thf('46', plain,
% 0.40/0.63      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.63  thf('47', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 0.40/0.63  thf('48', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(cc2_relat_1, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( v1_relat_1 @ A ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.63  thf('49', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.63          | (v1_relat_1 @ X0)
% 0.40/0.63          | ~ (v1_relat_1 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.63  thf('50', plain,
% 0.40/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.40/0.63  thf(fc6_relat_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.63  thf('51', plain,
% 0.40/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.40/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.63  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.63      inference('demod', [status(thm)], ['50', '51'])).
% 0.40/0.63  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('54', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(cc2_funct_2, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.63       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.40/0.63         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.40/0.63  thf('55', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.63         (~ (v1_funct_1 @ X16)
% 0.40/0.63          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.40/0.63          | (v2_funct_1 @ X16)
% 0.40/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.40/0.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.40/0.63  thf('56', plain,
% 0.40/0.63      (((v2_funct_1 @ sk_B)
% 0.40/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.40/0.63        | ~ (v1_funct_1 @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.40/0.63  thf('57', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('59', plain, ((v2_funct_1 @ sk_B)),
% 0.40/0.63      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.40/0.63  thf('60', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('61', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.63         (~ (v1_funct_1 @ X16)
% 0.40/0.63          | ~ (v3_funct_2 @ X16 @ X17 @ X18)
% 0.40/0.63          | (v2_funct_2 @ X16 @ X18)
% 0.40/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.40/0.63      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.40/0.63  thf('62', plain,
% 0.40/0.63      (((v2_funct_2 @ sk_B @ sk_A)
% 0.40/0.63        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.40/0.63        | ~ (v1_funct_1 @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.63  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('65', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.40/0.63      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.40/0.63  thf(d3_funct_2, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.40/0.63       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.40/0.63  thf('66', plain,
% 0.40/0.63      (![X19 : $i, X20 : $i]:
% 0.40/0.63         (~ (v2_funct_2 @ X20 @ X19)
% 0.40/0.63          | ((k2_relat_1 @ X20) = (X19))
% 0.40/0.63          | ~ (v5_relat_1 @ X20 @ X19)
% 0.40/0.63          | ~ (v1_relat_1 @ X20))),
% 0.40/0.63      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.40/0.63  thf('67', plain,
% 0.40/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.63        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.40/0.63        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.40/0.63  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.63      inference('demod', [status(thm)], ['50', '51'])).
% 0.40/0.63  thf('69', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(cc2_relset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.63  thf('70', plain,
% 0.40/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.63         ((v5_relat_1 @ X6 @ X8)
% 0.40/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.40/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.63  thf('71', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.40/0.63      inference('sup-', [status(thm)], ['69', '70'])).
% 0.40/0.63  thf('72', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['67', '68', '71'])).
% 0.40/0.63  thf('73', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('74', plain,
% 0.40/0.63      (![X38 : $i, X39 : $i]:
% 0.40/0.63         (((k1_relset_1 @ X38 @ X38 @ X39) = (X38))
% 0.40/0.63          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.40/0.63          | ~ (v1_funct_2 @ X39 @ X38 @ X38)
% 0.40/0.63          | ~ (v1_funct_1 @ X39))),
% 0.40/0.63      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.40/0.63  thf('75', plain,
% 0.40/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.63        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.40/0.63        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['73', '74'])).
% 0.40/0.63  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('77', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('78', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('79', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.63         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.40/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.63  thf('80', plain,
% 0.40/0.63      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.40/0.63      inference('sup-', [status(thm)], ['78', '79'])).
% 0.40/0.63  thf('81', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['75', '76', '77', '80'])).
% 0.40/0.63  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('83', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('84', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.63          | (v1_relat_1 @ X0)
% 0.40/0.63          | ~ (v1_relat_1 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.63  thf('85', plain,
% 0.40/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.40/0.63      inference('sup-', [status(thm)], ['83', '84'])).
% 0.40/0.63  thf('86', plain,
% 0.40/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.40/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.63  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.63      inference('demod', [status(thm)], ['85', '86'])).
% 0.40/0.63  thf('88', plain,
% 0.40/0.63      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.40/0.63        | ((sk_A) != (sk_A))
% 0.40/0.63        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.40/0.63      inference('demod', [status(thm)],
% 0.40/0.63                ['38', '47', '52', '53', '59', '72', '81', '82', '87'])).
% 0.40/0.63  thf('89', plain, (((sk_C) = (k2_funct_1 @ sk_B))),
% 0.40/0.63      inference('simplify', [status(thm)], ['88'])).
% 0.40/0.63  thf('90', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('91', plain,
% 0.40/0.63      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.63          | (r2_relset_1 @ X13 @ X14 @ X12 @ X15)
% 0.40/0.63          | ((X12) != (X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.40/0.63  thf('92', plain,
% 0.40/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.63         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.40/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.40/0.63      inference('simplify', [status(thm)], ['91'])).
% 0.40/0.63  thf('93', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.40/0.63      inference('sup-', [status(thm)], ['90', '92'])).
% 0.40/0.63  thf('94', plain, ($false),
% 0.40/0.63      inference('demod', [status(thm)], ['8', '89', '93'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
