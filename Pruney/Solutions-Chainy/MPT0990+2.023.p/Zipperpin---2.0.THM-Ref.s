%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qgniOW05y5

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:57 EST 2020

% Result     : Theorem 4.30s
% Output     : Refutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 512 expanded)
%              Number of leaves         :   41 ( 173 expanded)
%              Depth                    :   17
%              Number of atoms          : 1759 (9677 expanded)
%              Number of equality atoms :  121 ( 658 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf('31',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X37 ) @ X37 )
        = ( k6_partfun1 @ X36 ) )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_relset_1 @ X38 @ X36 @ X37 )
       != X36 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('41',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X37 ) @ X37 )
        = ( k6_relat_1 @ X36 ) )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_relset_1 @ X38 @ X36 @ X37 )
       != X36 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['38','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','55','56','57'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('70',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('71',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('74',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['68','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('84',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_D
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['59','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('87',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('89',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D ) @ X0 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('94',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('95',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('96',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_D )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_D )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','101'])).

thf('103',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('104',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ( ( k5_relat_1 @ X37 @ ( k2_funct_1 @ X37 ) )
        = ( k6_partfun1 @ X38 ) )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_relset_1 @ X38 @ X36 @ X37 )
       != X36 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('107',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('108',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ( ( k5_relat_1 @ X37 @ ( k2_funct_1 @ X37 ) )
        = ( k6_relat_1 @ X38 ) )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_relset_1 @ X38 @ X36 @ X37 )
       != X36 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['104','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf('124',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('125',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['122','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('138',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','58','102','103','133','134','135','136','137'])).

thf('139',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qgniOW05y5
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:22:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.30/4.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.30/4.49  % Solved by: fo/fo7.sh
% 4.30/4.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.30/4.49  % done 1693 iterations in 4.023s
% 4.30/4.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.30/4.49  % SZS output start Refutation
% 4.30/4.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.30/4.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.30/4.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.30/4.49  thf(sk_C_type, type, sk_C: $i).
% 4.30/4.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.30/4.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.30/4.49  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.30/4.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.30/4.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.30/4.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.30/4.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.30/4.49  thf(sk_A_type, type, sk_A: $i).
% 4.30/4.49  thf(sk_B_type, type, sk_B: $i).
% 4.30/4.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.30/4.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.30/4.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.30/4.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.30/4.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.30/4.49  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.30/4.49  thf(sk_D_type, type, sk_D: $i).
% 4.30/4.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.30/4.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.30/4.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.30/4.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.30/4.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.30/4.49  thf(t36_funct_2, conjecture,
% 4.30/4.49    (![A:$i,B:$i,C:$i]:
% 4.30/4.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.30/4.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.30/4.49       ( ![D:$i]:
% 4.30/4.49         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.30/4.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.30/4.49           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.30/4.49               ( r2_relset_1 @
% 4.30/4.49                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.30/4.49                 ( k6_partfun1 @ A ) ) & 
% 4.30/4.49               ( v2_funct_1 @ C ) ) =>
% 4.30/4.49             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.30/4.49               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 4.30/4.49  thf(zf_stmt_0, negated_conjecture,
% 4.30/4.49    (~( ![A:$i,B:$i,C:$i]:
% 4.30/4.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.30/4.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.30/4.49          ( ![D:$i]:
% 4.30/4.49            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.30/4.49                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.30/4.49              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.30/4.49                  ( r2_relset_1 @
% 4.30/4.49                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.30/4.49                    ( k6_partfun1 @ A ) ) & 
% 4.30/4.49                  ( v2_funct_1 @ C ) ) =>
% 4.30/4.49                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.30/4.49                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 4.30/4.49    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 4.30/4.49  thf('0', plain,
% 4.30/4.49      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.30/4.49        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.30/4.49        (k6_partfun1 @ sk_A))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf(redefinition_k6_partfun1, axiom,
% 4.30/4.49    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.30/4.49  thf('1', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 4.30/4.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.30/4.49  thf('2', plain,
% 4.30/4.49      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.30/4.49        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.30/4.49        (k6_relat_1 @ sk_A))),
% 4.30/4.49      inference('demod', [status(thm)], ['0', '1'])).
% 4.30/4.49  thf('3', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('4', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf(redefinition_k1_partfun1, axiom,
% 4.30/4.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.30/4.49     ( ( ( v1_funct_1 @ E ) & 
% 4.30/4.49         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.30/4.49         ( v1_funct_1 @ F ) & 
% 4.30/4.49         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.30/4.49       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.30/4.49  thf('5', plain,
% 4.30/4.49      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 4.30/4.49         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 4.30/4.49          | ~ (v1_funct_1 @ X29)
% 4.30/4.49          | ~ (v1_funct_1 @ X32)
% 4.30/4.49          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 4.30/4.49          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 4.30/4.49              = (k5_relat_1 @ X29 @ X32)))),
% 4.30/4.49      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.30/4.49  thf('6', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.30/4.49            = (k5_relat_1 @ sk_C @ X0))
% 4.30/4.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ sk_C))),
% 4.30/4.49      inference('sup-', [status(thm)], ['4', '5'])).
% 4.30/4.49  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('8', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.30/4.49            = (k5_relat_1 @ sk_C @ X0))
% 4.30/4.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.30/4.49          | ~ (v1_funct_1 @ X0))),
% 4.30/4.49      inference('demod', [status(thm)], ['6', '7'])).
% 4.30/4.49  thf('9', plain,
% 4.30/4.49      ((~ (v1_funct_1 @ sk_D)
% 4.30/4.49        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.30/4.49            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.30/4.49      inference('sup-', [status(thm)], ['3', '8'])).
% 4.30/4.49  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('11', plain,
% 4.30/4.49      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.30/4.49         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.30/4.49      inference('demod', [status(thm)], ['9', '10'])).
% 4.30/4.49  thf('12', plain,
% 4.30/4.49      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.30/4.49        (k6_relat_1 @ sk_A))),
% 4.30/4.49      inference('demod', [status(thm)], ['2', '11'])).
% 4.30/4.49  thf('13', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('14', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf(dt_k1_partfun1, axiom,
% 4.30/4.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.30/4.49     ( ( ( v1_funct_1 @ E ) & 
% 4.30/4.49         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.30/4.49         ( v1_funct_1 @ F ) & 
% 4.30/4.49         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.30/4.49       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.30/4.49         ( m1_subset_1 @
% 4.30/4.49           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.30/4.49           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.30/4.49  thf('15', plain,
% 4.30/4.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 4.30/4.49         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 4.30/4.49          | ~ (v1_funct_1 @ X21)
% 4.30/4.49          | ~ (v1_funct_1 @ X24)
% 4.30/4.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.30/4.49          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 4.30/4.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 4.30/4.49      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.30/4.49  thf('16', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.30/4.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.30/4.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.30/4.49          | ~ (v1_funct_1 @ X1)
% 4.30/4.49          | ~ (v1_funct_1 @ sk_C))),
% 4.30/4.49      inference('sup-', [status(thm)], ['14', '15'])).
% 4.30/4.49  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('18', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.30/4.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.30/4.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.30/4.49          | ~ (v1_funct_1 @ X1))),
% 4.30/4.49      inference('demod', [status(thm)], ['16', '17'])).
% 4.30/4.49  thf('19', plain,
% 4.30/4.49      ((~ (v1_funct_1 @ sk_D)
% 4.30/4.49        | (m1_subset_1 @ 
% 4.30/4.49           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.30/4.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.30/4.49      inference('sup-', [status(thm)], ['13', '18'])).
% 4.30/4.49  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('21', plain,
% 4.30/4.49      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.30/4.49         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.30/4.49      inference('demod', [status(thm)], ['9', '10'])).
% 4.30/4.49  thf('22', plain,
% 4.30/4.49      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.30/4.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.30/4.49      inference('demod', [status(thm)], ['19', '20', '21'])).
% 4.30/4.49  thf(redefinition_r2_relset_1, axiom,
% 4.30/4.49    (![A:$i,B:$i,C:$i,D:$i]:
% 4.30/4.49     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.30/4.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.30/4.49       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.30/4.49  thf('23', plain,
% 4.30/4.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 4.30/4.49         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 4.30/4.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 4.30/4.49          | ((X17) = (X20))
% 4.30/4.49          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 4.30/4.49      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.30/4.49  thf('24', plain,
% 4.30/4.49      (![X0 : $i]:
% 4.30/4.49         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 4.30/4.49          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 4.30/4.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.30/4.49      inference('sup-', [status(thm)], ['22', '23'])).
% 4.30/4.49  thf('25', plain,
% 4.30/4.49      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 4.30/4.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.30/4.49        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 4.30/4.49      inference('sup-', [status(thm)], ['12', '24'])).
% 4.30/4.49  thf(dt_k6_partfun1, axiom,
% 4.30/4.49    (![A:$i]:
% 4.30/4.49     ( ( m1_subset_1 @
% 4.30/4.49         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.30/4.49       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.30/4.49  thf('26', plain,
% 4.30/4.49      (![X28 : $i]:
% 4.30/4.49         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 4.30/4.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 4.30/4.49      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.30/4.49  thf('27', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 4.30/4.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.30/4.49  thf('28', plain,
% 4.30/4.49      (![X28 : $i]:
% 4.30/4.49         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 4.30/4.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 4.30/4.49      inference('demod', [status(thm)], ['26', '27'])).
% 4.30/4.49  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 4.30/4.49      inference('demod', [status(thm)], ['25', '28'])).
% 4.30/4.49  thf(dt_k2_funct_1, axiom,
% 4.30/4.49    (![A:$i]:
% 4.30/4.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.30/4.49       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.30/4.49         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.30/4.49  thf('30', plain,
% 4.30/4.49      (![X8 : $i]:
% 4.30/4.49         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 4.30/4.49          | ~ (v1_funct_1 @ X8)
% 4.30/4.49          | ~ (v1_relat_1 @ X8))),
% 4.30/4.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.30/4.49  thf(t61_funct_1, axiom,
% 4.30/4.49    (![A:$i]:
% 4.30/4.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.30/4.49       ( ( v2_funct_1 @ A ) =>
% 4.30/4.49         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 4.30/4.49             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 4.30/4.49           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 4.30/4.49             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.30/4.49  thf('31', plain,
% 4.30/4.49      (![X10 : $i]:
% 4.30/4.49         (~ (v2_funct_1 @ X10)
% 4.30/4.49          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 4.30/4.49              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 4.30/4.49          | ~ (v1_funct_1 @ X10)
% 4.30/4.49          | ~ (v1_relat_1 @ X10))),
% 4.30/4.49      inference('cnf', [status(esa)], [t61_funct_1])).
% 4.30/4.49  thf(t55_relat_1, axiom,
% 4.30/4.49    (![A:$i]:
% 4.30/4.49     ( ( v1_relat_1 @ A ) =>
% 4.30/4.49       ( ![B:$i]:
% 4.30/4.49         ( ( v1_relat_1 @ B ) =>
% 4.30/4.49           ( ![C:$i]:
% 4.30/4.49             ( ( v1_relat_1 @ C ) =>
% 4.30/4.49               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 4.30/4.49                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 4.30/4.49  thf('32', plain,
% 4.30/4.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X2)
% 4.30/4.49          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 4.30/4.49              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 4.30/4.49          | ~ (v1_relat_1 @ X4)
% 4.30/4.49          | ~ (v1_relat_1 @ X3))),
% 4.30/4.49      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.30/4.49  thf('33', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i]:
% 4.30/4.49         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 4.30/4.49            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v2_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.30/4.49          | ~ (v1_relat_1 @ X1)
% 4.30/4.49          | ~ (v1_relat_1 @ X0))),
% 4.30/4.49      inference('sup+', [status(thm)], ['31', '32'])).
% 4.30/4.49  thf('34', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X1)
% 4.30/4.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.30/4.49          | ~ (v2_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 4.30/4.49              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 4.30/4.49      inference('simplify', [status(thm)], ['33'])).
% 4.30/4.49  thf('35', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 4.30/4.49              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v2_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ X1))),
% 4.30/4.49      inference('sup-', [status(thm)], ['30', '34'])).
% 4.30/4.49  thf('36', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X1)
% 4.30/4.49          | ~ (v2_funct_1 @ X0)
% 4.30/4.49          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 4.30/4.49              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ X0))),
% 4.30/4.49      inference('simplify', [status(thm)], ['35'])).
% 4.30/4.49  thf('37', plain,
% 4.30/4.49      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 4.30/4.49          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 4.30/4.49        | ~ (v1_relat_1 @ sk_C)
% 4.30/4.49        | ~ (v1_funct_1 @ sk_C)
% 4.30/4.49        | ~ (v2_funct_1 @ sk_C)
% 4.30/4.49        | ~ (v1_relat_1 @ sk_D))),
% 4.30/4.49      inference('sup+', [status(thm)], ['29', '36'])).
% 4.30/4.49  thf('38', plain,
% 4.30/4.49      (![X10 : $i]:
% 4.30/4.49         (~ (v2_funct_1 @ X10)
% 4.30/4.49          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 4.30/4.49              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 4.30/4.49          | ~ (v1_funct_1 @ X10)
% 4.30/4.49          | ~ (v1_relat_1 @ X10))),
% 4.30/4.49      inference('cnf', [status(esa)], [t61_funct_1])).
% 4.30/4.49  thf('39', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf(t35_funct_2, axiom,
% 4.30/4.49    (![A:$i,B:$i,C:$i]:
% 4.30/4.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.30/4.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.30/4.49       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 4.30/4.49         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.30/4.49           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 4.30/4.49             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 4.30/4.49  thf('40', plain,
% 4.30/4.49      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.30/4.49         (((X36) = (k1_xboole_0))
% 4.30/4.49          | ~ (v1_funct_1 @ X37)
% 4.30/4.49          | ~ (v1_funct_2 @ X37 @ X38 @ X36)
% 4.30/4.49          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 4.30/4.49          | ((k5_relat_1 @ (k2_funct_1 @ X37) @ X37) = (k6_partfun1 @ X36))
% 4.30/4.49          | ~ (v2_funct_1 @ X37)
% 4.30/4.49          | ((k2_relset_1 @ X38 @ X36 @ X37) != (X36)))),
% 4.30/4.49      inference('cnf', [status(esa)], [t35_funct_2])).
% 4.30/4.49  thf('41', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 4.30/4.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.30/4.49  thf('42', plain,
% 4.30/4.49      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.30/4.49         (((X36) = (k1_xboole_0))
% 4.30/4.49          | ~ (v1_funct_1 @ X37)
% 4.30/4.49          | ~ (v1_funct_2 @ X37 @ X38 @ X36)
% 4.30/4.49          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 4.30/4.49          | ((k5_relat_1 @ (k2_funct_1 @ X37) @ X37) = (k6_relat_1 @ X36))
% 4.30/4.49          | ~ (v2_funct_1 @ X37)
% 4.30/4.49          | ((k2_relset_1 @ X38 @ X36 @ X37) != (X36)))),
% 4.30/4.49      inference('demod', [status(thm)], ['40', '41'])).
% 4.30/4.49  thf('43', plain,
% 4.30/4.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 4.30/4.49        | ~ (v2_funct_1 @ sk_C)
% 4.30/4.49        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 4.30/4.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.30/4.49        | ~ (v1_funct_1 @ sk_C)
% 4.30/4.49        | ((sk_B) = (k1_xboole_0)))),
% 4.30/4.49      inference('sup-', [status(thm)], ['39', '42'])).
% 4.30/4.49  thf('44', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('46', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('48', plain,
% 4.30/4.49      ((((sk_B) != (sk_B))
% 4.30/4.49        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 4.30/4.49        | ((sk_B) = (k1_xboole_0)))),
% 4.30/4.49      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 4.30/4.49  thf('49', plain,
% 4.30/4.49      ((((sk_B) = (k1_xboole_0))
% 4.30/4.49        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 4.30/4.49      inference('simplify', [status(thm)], ['48'])).
% 4.30/4.49  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('51', plain,
% 4.30/4.49      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 4.30/4.49      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 4.30/4.49  thf('52', plain,
% 4.30/4.49      ((((k6_relat_1 @ (k2_relat_1 @ sk_C)) = (k6_relat_1 @ sk_B))
% 4.30/4.49        | ~ (v1_relat_1 @ sk_C)
% 4.30/4.49        | ~ (v1_funct_1 @ sk_C)
% 4.30/4.49        | ~ (v2_funct_1 @ sk_C))),
% 4.30/4.49      inference('sup+', [status(thm)], ['38', '51'])).
% 4.30/4.49  thf('53', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf(cc1_relset_1, axiom,
% 4.30/4.49    (![A:$i,B:$i,C:$i]:
% 4.30/4.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.30/4.49       ( v1_relat_1 @ C ) ))).
% 4.30/4.49  thf('54', plain,
% 4.30/4.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.30/4.49         ((v1_relat_1 @ X11)
% 4.30/4.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 4.30/4.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.30/4.49  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 4.30/4.49      inference('sup-', [status(thm)], ['53', '54'])).
% 4.30/4.49  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('58', plain,
% 4.30/4.49      (((k6_relat_1 @ (k2_relat_1 @ sk_C)) = (k6_relat_1 @ sk_B))),
% 4.30/4.49      inference('demod', [status(thm)], ['52', '55', '56', '57'])).
% 4.30/4.49  thf(t80_relat_1, axiom,
% 4.30/4.49    (![A:$i]:
% 4.30/4.49     ( ( v1_relat_1 @ A ) =>
% 4.30/4.49       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 4.30/4.49  thf('59', plain,
% 4.30/4.49      (![X5 : $i]:
% 4.30/4.49         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 4.30/4.49          | ~ (v1_relat_1 @ X5))),
% 4.30/4.49      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.30/4.49  thf('60', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf(cc2_relset_1, axiom,
% 4.30/4.49    (![A:$i,B:$i,C:$i]:
% 4.30/4.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.30/4.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.30/4.49  thf('61', plain,
% 4.30/4.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.30/4.49         ((v4_relat_1 @ X14 @ X15)
% 4.30/4.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 4.30/4.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.30/4.49  thf('62', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 4.30/4.49      inference('sup-', [status(thm)], ['60', '61'])).
% 4.30/4.49  thf(t209_relat_1, axiom,
% 4.30/4.49    (![A:$i,B:$i]:
% 4.30/4.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.30/4.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 4.30/4.49  thf('63', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i]:
% 4.30/4.49         (((X0) = (k7_relat_1 @ X0 @ X1))
% 4.30/4.49          | ~ (v4_relat_1 @ X0 @ X1)
% 4.30/4.49          | ~ (v1_relat_1 @ X0))),
% 4.30/4.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 4.30/4.49  thf('64', plain,
% 4.30/4.49      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 4.30/4.49      inference('sup-', [status(thm)], ['62', '63'])).
% 4.30/4.49  thf('65', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('66', plain,
% 4.30/4.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.30/4.49         ((v1_relat_1 @ X11)
% 4.30/4.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 4.30/4.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.30/4.49  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 4.30/4.49      inference('sup-', [status(thm)], ['65', '66'])).
% 4.30/4.49  thf('68', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 4.30/4.49      inference('demod', [status(thm)], ['64', '67'])).
% 4.30/4.49  thf('69', plain,
% 4.30/4.49      (![X5 : $i]:
% 4.30/4.49         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 4.30/4.49          | ~ (v1_relat_1 @ X5))),
% 4.30/4.49      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.30/4.49  thf(t94_relat_1, axiom,
% 4.30/4.49    (![A:$i,B:$i]:
% 4.30/4.49     ( ( v1_relat_1 @ B ) =>
% 4.30/4.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 4.30/4.49  thf('70', plain,
% 4.30/4.49      (![X6 : $i, X7 : $i]:
% 4.30/4.49         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 4.30/4.49          | ~ (v1_relat_1 @ X7))),
% 4.30/4.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.30/4.49  thf('71', plain,
% 4.30/4.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X2)
% 4.30/4.49          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 4.30/4.49              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 4.30/4.49          | ~ (v1_relat_1 @ X4)
% 4.30/4.49          | ~ (v1_relat_1 @ X3))),
% 4.30/4.49      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.30/4.49  thf('72', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.30/4.49            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 4.30/4.49          | ~ (v1_relat_1 @ X1)
% 4.30/4.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.30/4.49          | ~ (v1_relat_1 @ X2)
% 4.30/4.49          | ~ (v1_relat_1 @ X1))),
% 4.30/4.49      inference('sup+', [status(thm)], ['70', '71'])).
% 4.30/4.49  thf('73', plain,
% 4.30/4.49      (![X28 : $i]:
% 4.30/4.49         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 4.30/4.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 4.30/4.49      inference('demod', [status(thm)], ['26', '27'])).
% 4.30/4.49  thf('74', plain,
% 4.30/4.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.30/4.49         ((v1_relat_1 @ X11)
% 4.30/4.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 4.30/4.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.30/4.49  thf('75', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 4.30/4.49      inference('sup-', [status(thm)], ['73', '74'])).
% 4.30/4.49  thf('76', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.30/4.49            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 4.30/4.49          | ~ (v1_relat_1 @ X1)
% 4.30/4.49          | ~ (v1_relat_1 @ X2)
% 4.30/4.49          | ~ (v1_relat_1 @ X1))),
% 4.30/4.49      inference('demod', [status(thm)], ['72', '75'])).
% 4.30/4.49  thf('77', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X2)
% 4.30/4.49          | ~ (v1_relat_1 @ X1)
% 4.30/4.49          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.30/4.49              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.30/4.49      inference('simplify', [status(thm)], ['76'])).
% 4.30/4.49  thf('78', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i]:
% 4.30/4.49         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 4.30/4.49            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 4.30/4.49            = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 4.30/4.49      inference('sup+', [status(thm)], ['69', '77'])).
% 4.30/4.49  thf('79', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 4.30/4.49      inference('sup-', [status(thm)], ['73', '74'])).
% 4.30/4.49  thf('80', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i]:
% 4.30/4.49         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 4.30/4.49            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 4.30/4.49            = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ X0))),
% 4.30/4.49      inference('demod', [status(thm)], ['78', '79'])).
% 4.30/4.49  thf('81', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X0)
% 4.30/4.49          | ((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 4.30/4.49              (k6_relat_1 @ (k2_relat_1 @ X0)))
% 4.30/4.49              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 4.30/4.49      inference('simplify', [status(thm)], ['80'])).
% 4.30/4.49  thf('82', plain,
% 4.30/4.49      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 4.30/4.49          = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D))
% 4.30/4.49        | ~ (v1_relat_1 @ sk_D))),
% 4.30/4.49      inference('sup+', [status(thm)], ['68', '81'])).
% 4.30/4.49  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 4.30/4.49      inference('sup-', [status(thm)], ['65', '66'])).
% 4.30/4.49  thf('84', plain,
% 4.30/4.49      (((k5_relat_1 @ sk_D @ (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 4.30/4.49         = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D))),
% 4.30/4.49      inference('demod', [status(thm)], ['82', '83'])).
% 4.30/4.49  thf('85', plain,
% 4.30/4.49      ((((sk_D) = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D))
% 4.30/4.49        | ~ (v1_relat_1 @ sk_D))),
% 4.30/4.49      inference('sup+', [status(thm)], ['59', '84'])).
% 4.30/4.49  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 4.30/4.49      inference('sup-', [status(thm)], ['65', '66'])).
% 4.30/4.49  thf('87', plain, (((sk_D) = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D))),
% 4.30/4.49      inference('demod', [status(thm)], ['85', '86'])).
% 4.30/4.49  thf('88', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X2)
% 4.30/4.49          | ~ (v1_relat_1 @ X1)
% 4.30/4.49          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.30/4.49              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.30/4.49      inference('simplify', [status(thm)], ['76'])).
% 4.30/4.49  thf('89', plain,
% 4.30/4.49      (![X6 : $i, X7 : $i]:
% 4.30/4.49         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 4.30/4.49          | ~ (v1_relat_1 @ X7))),
% 4.30/4.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.30/4.49  thf('90', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 4.30/4.49            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 4.30/4.49          | ~ (v1_relat_1 @ X2)
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 4.30/4.49      inference('sup+', [status(thm)], ['88', '89'])).
% 4.30/4.49  thf('91', plain,
% 4.30/4.49      (![X0 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ sk_D)
% 4.30/4.49          | ~ (v1_relat_1 @ sk_D)
% 4.30/4.49          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 4.30/4.49          | ((k7_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) @ X0)
% 4.30/4.49              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_D)))),
% 4.30/4.49      inference('sup-', [status(thm)], ['87', '90'])).
% 4.30/4.49  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 4.30/4.49      inference('sup-', [status(thm)], ['65', '66'])).
% 4.30/4.49  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 4.30/4.49      inference('sup-', [status(thm)], ['65', '66'])).
% 4.30/4.49  thf('94', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 4.30/4.49      inference('sup-', [status(thm)], ['73', '74'])).
% 4.30/4.49  thf('95', plain, (((sk_D) = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D))),
% 4.30/4.49      inference('demod', [status(thm)], ['85', '86'])).
% 4.30/4.49  thf('96', plain, (((sk_D) = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D))),
% 4.30/4.49      inference('demod', [status(thm)], ['85', '86'])).
% 4.30/4.49  thf('97', plain,
% 4.30/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X2)
% 4.30/4.49          | ~ (v1_relat_1 @ X1)
% 4.30/4.49          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.30/4.49              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.30/4.49      inference('simplify', [status(thm)], ['76'])).
% 4.30/4.49  thf('98', plain,
% 4.30/4.49      (![X0 : $i]:
% 4.30/4.49         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_D)
% 4.30/4.49            = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_D))
% 4.30/4.49          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 4.30/4.49          | ~ (v1_relat_1 @ sk_D))),
% 4.30/4.49      inference('sup+', [status(thm)], ['96', '97'])).
% 4.30/4.49  thf('99', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 4.30/4.49      inference('sup-', [status(thm)], ['73', '74'])).
% 4.30/4.49  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 4.30/4.49      inference('sup-', [status(thm)], ['65', '66'])).
% 4.30/4.49  thf('101', plain,
% 4.30/4.49      (![X0 : $i]:
% 4.30/4.49         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_D)
% 4.30/4.49           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_D))),
% 4.30/4.49      inference('demod', [status(thm)], ['98', '99', '100'])).
% 4.30/4.49  thf('102', plain,
% 4.30/4.49      (![X0 : $i]:
% 4.30/4.49         ((k7_relat_1 @ sk_D @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_D))),
% 4.30/4.49      inference('demod', [status(thm)], ['91', '92', '93', '94', '95', '101'])).
% 4.30/4.49  thf('103', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 4.30/4.49      inference('demod', [status(thm)], ['64', '67'])).
% 4.30/4.49  thf('104', plain,
% 4.30/4.49      (![X10 : $i]:
% 4.30/4.49         (~ (v2_funct_1 @ X10)
% 4.30/4.49          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 4.30/4.49              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 4.30/4.49          | ~ (v1_funct_1 @ X10)
% 4.30/4.49          | ~ (v1_relat_1 @ X10))),
% 4.30/4.49      inference('cnf', [status(esa)], [t61_funct_1])).
% 4.30/4.49  thf('105', plain,
% 4.30/4.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('106', plain,
% 4.30/4.49      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.30/4.49         (((X36) = (k1_xboole_0))
% 4.30/4.49          | ~ (v1_funct_1 @ X37)
% 4.30/4.49          | ~ (v1_funct_2 @ X37 @ X38 @ X36)
% 4.30/4.49          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 4.30/4.49          | ((k5_relat_1 @ X37 @ (k2_funct_1 @ X37)) = (k6_partfun1 @ X38))
% 4.30/4.49          | ~ (v2_funct_1 @ X37)
% 4.30/4.49          | ((k2_relset_1 @ X38 @ X36 @ X37) != (X36)))),
% 4.30/4.49      inference('cnf', [status(esa)], [t35_funct_2])).
% 4.30/4.49  thf('107', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 4.30/4.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.30/4.49  thf('108', plain,
% 4.30/4.49      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.30/4.49         (((X36) = (k1_xboole_0))
% 4.30/4.49          | ~ (v1_funct_1 @ X37)
% 4.30/4.49          | ~ (v1_funct_2 @ X37 @ X38 @ X36)
% 4.30/4.49          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 4.30/4.49          | ((k5_relat_1 @ X37 @ (k2_funct_1 @ X37)) = (k6_relat_1 @ X38))
% 4.30/4.49          | ~ (v2_funct_1 @ X37)
% 4.30/4.49          | ((k2_relset_1 @ X38 @ X36 @ X37) != (X36)))),
% 4.30/4.49      inference('demod', [status(thm)], ['106', '107'])).
% 4.30/4.49  thf('109', plain,
% 4.30/4.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 4.30/4.49        | ~ (v2_funct_1 @ sk_C)
% 4.30/4.49        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 4.30/4.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.30/4.49        | ~ (v1_funct_1 @ sk_C)
% 4.30/4.49        | ((sk_B) = (k1_xboole_0)))),
% 4.30/4.49      inference('sup-', [status(thm)], ['105', '108'])).
% 4.30/4.49  thf('110', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('112', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('114', plain,
% 4.30/4.49      ((((sk_B) != (sk_B))
% 4.30/4.49        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 4.30/4.49        | ((sk_B) = (k1_xboole_0)))),
% 4.30/4.49      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 4.30/4.49  thf('115', plain,
% 4.30/4.49      ((((sk_B) = (k1_xboole_0))
% 4.30/4.49        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 4.30/4.49      inference('simplify', [status(thm)], ['114'])).
% 4.30/4.49  thf('116', plain, (((sk_B) != (k1_xboole_0))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('117', plain,
% 4.30/4.49      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 4.30/4.49      inference('simplify_reflect-', [status(thm)], ['115', '116'])).
% 4.30/4.49  thf('118', plain,
% 4.30/4.49      ((((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 4.30/4.49        | ~ (v1_relat_1 @ sk_C)
% 4.30/4.49        | ~ (v1_funct_1 @ sk_C)
% 4.30/4.49        | ~ (v2_funct_1 @ sk_C))),
% 4.30/4.49      inference('sup+', [status(thm)], ['104', '117'])).
% 4.30/4.49  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 4.30/4.49      inference('sup-', [status(thm)], ['53', '54'])).
% 4.30/4.49  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('122', plain,
% 4.30/4.49      (((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 4.30/4.49      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 4.30/4.49  thf('123', plain,
% 4.30/4.49      (![X8 : $i]:
% 4.30/4.49         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 4.30/4.49          | ~ (v1_funct_1 @ X8)
% 4.30/4.49          | ~ (v1_relat_1 @ X8))),
% 4.30/4.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.30/4.49  thf(t55_funct_1, axiom,
% 4.30/4.49    (![A:$i]:
% 4.30/4.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.30/4.49       ( ( v2_funct_1 @ A ) =>
% 4.30/4.49         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.30/4.49           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.30/4.49  thf('124', plain,
% 4.30/4.49      (![X9 : $i]:
% 4.30/4.49         (~ (v2_funct_1 @ X9)
% 4.30/4.49          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 4.30/4.49          | ~ (v1_funct_1 @ X9)
% 4.30/4.49          | ~ (v1_relat_1 @ X9))),
% 4.30/4.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.30/4.49  thf('125', plain,
% 4.30/4.49      (![X5 : $i]:
% 4.30/4.49         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 4.30/4.49          | ~ (v1_relat_1 @ X5))),
% 4.30/4.49      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.30/4.49  thf('126', plain,
% 4.30/4.49      (![X0 : $i]:
% 4.30/4.49         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 4.30/4.49            = (k2_funct_1 @ X0))
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v2_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.30/4.49      inference('sup+', [status(thm)], ['124', '125'])).
% 4.30/4.49  thf('127', plain,
% 4.30/4.49      (![X0 : $i]:
% 4.30/4.49         (~ (v1_relat_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v2_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ X0)
% 4.30/4.49          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 4.30/4.49              = (k2_funct_1 @ X0)))),
% 4.30/4.49      inference('sup-', [status(thm)], ['123', '126'])).
% 4.30/4.49  thf('128', plain,
% 4.30/4.49      (![X0 : $i]:
% 4.30/4.49         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 4.30/4.49            = (k2_funct_1 @ X0))
% 4.30/4.49          | ~ (v2_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_funct_1 @ X0)
% 4.30/4.49          | ~ (v1_relat_1 @ X0))),
% 4.30/4.49      inference('simplify', [status(thm)], ['127'])).
% 4.30/4.49  thf('129', plain,
% 4.30/4.49      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 4.30/4.49          = (k2_funct_1 @ sk_C))
% 4.30/4.49        | ~ (v1_relat_1 @ sk_C)
% 4.30/4.49        | ~ (v1_funct_1 @ sk_C)
% 4.30/4.49        | ~ (v2_funct_1 @ sk_C))),
% 4.30/4.49      inference('sup+', [status(thm)], ['122', '128'])).
% 4.30/4.49  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 4.30/4.49      inference('sup-', [status(thm)], ['53', '54'])).
% 4.30/4.49  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('133', plain,
% 4.30/4.49      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 4.30/4.49         = (k2_funct_1 @ sk_C))),
% 4.30/4.49      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 4.30/4.49  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 4.30/4.49      inference('sup-', [status(thm)], ['53', '54'])).
% 4.30/4.49  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('137', plain, ((v1_relat_1 @ sk_D)),
% 4.30/4.49      inference('sup-', [status(thm)], ['65', '66'])).
% 4.30/4.49  thf('138', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 4.30/4.49      inference('demod', [status(thm)],
% 4.30/4.49                ['37', '58', '102', '103', '133', '134', '135', '136', '137'])).
% 4.30/4.49  thf('139', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 4.30/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.30/4.49  thf('140', plain, ($false),
% 4.30/4.49      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 4.30/4.49  
% 4.30/4.49  % SZS output end Refutation
% 4.30/4.49  
% 4.30/4.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
