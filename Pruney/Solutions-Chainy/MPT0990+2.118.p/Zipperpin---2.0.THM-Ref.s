%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lzN8ibJID8

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:14 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 411 expanded)
%              Number of leaves         :   41 ( 142 expanded)
%              Depth                    :   15
%              Number of atoms          : 1323 (9557 expanded)
%              Number of equality atoms :  103 ( 705 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('34',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20','37'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('41',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ( ( k5_relat_1 @ X41 @ ( k2_funct_1 @ X41 ) )
        = ( k6_partfun1 @ X42 ) )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_relset_1 @ X42 @ X40 @ X41 )
       != X40 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('46',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('56',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','59','64','65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X41 ) @ X41 )
        = ( k6_partfun1 @ X40 ) )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_relset_1 @ X42 @ X40 @ X41 )
       != X40 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('72',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('81',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 ) )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('82',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('90',plain,
    ( ( sk_A != sk_A )
    | ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','43','67','68','69','87','88','89'])).

thf('91',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','91'])).

thf('93',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20','37'])).

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

thf('94',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X17
        = ( k2_funct_1 @ X18 ) )
      | ( ( k5_relat_1 @ X18 @ X17 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ( ( k2_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('95',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X17
        = ( k2_funct_1 @ X18 ) )
      | ( ( k5_relat_1 @ X18 @ X17 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X18 ) ) )
      | ( ( k2_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','59','64','65','66'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('105',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103','104'])).

thf('106',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_B
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lzN8ibJID8
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 287 iterations in 0.289s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.54/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.54/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.76  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.54/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.76  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.54/0.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.54/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.76  thf(t36_funct_2, conjecture,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76       ( ![D:$i]:
% 0.54/0.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.54/0.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.54/0.76           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.54/0.76               ( r2_relset_1 @
% 0.54/0.76                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.54/0.76                 ( k6_partfun1 @ A ) ) & 
% 0.54/0.76               ( v2_funct_1 @ C ) ) =>
% 0.54/0.76             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.76               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76          ( ![D:$i]:
% 0.54/0.76            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.54/0.76                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.54/0.76              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.54/0.76                  ( r2_relset_1 @
% 0.54/0.76                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.54/0.76                    ( k6_partfun1 @ A ) ) & 
% 0.54/0.76                  ( v2_funct_1 @ C ) ) =>
% 0.54/0.76                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.76                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc2_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.76         ((v4_relat_1 @ X19 @ X20)
% 0.54/0.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.76  thf('2', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.54/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.76  thf(d18_relat_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ B ) =>
% 0.54/0.76       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      (![X5 : $i, X6 : $i]:
% 0.54/0.76         (~ (v4_relat_1 @ X5 @ X6)
% 0.54/0.76          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.54/0.76          | ~ (v1_relat_1 @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.76  thf('4', plain,
% 0.54/0.76      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.54/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.76  thf('5', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc2_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.76  thf('6', plain,
% 0.54/0.76      (![X3 : $i, X4 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.54/0.76          | (v1_relat_1 @ X3)
% 0.54/0.76          | ~ (v1_relat_1 @ X4))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.76  thf('7', plain,
% 0.54/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.76  thf(fc6_relat_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.76  thf('8', plain,
% 0.54/0.76      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.54/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.76  thf('9', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.76      inference('demod', [status(thm)], ['7', '8'])).
% 0.54/0.76  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.54/0.76      inference('demod', [status(thm)], ['4', '9'])).
% 0.54/0.76  thf(d10_xboole_0, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      (![X0 : $i, X2 : $i]:
% 0.54/0.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.76  thf('12', plain,
% 0.54/0.76      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_D))
% 0.54/0.76        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.76  thf('13', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(redefinition_k1_partfun1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.76     ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.76         ( v1_funct_1 @ F ) & 
% 0.54/0.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.54/0.76       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.54/0.76  thf('15', plain,
% 0.54/0.76      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.54/0.76          | ~ (v1_funct_1 @ X33)
% 0.54/0.76          | ~ (v1_funct_1 @ X36)
% 0.54/0.76          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.54/0.76          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 0.54/0.76              = (k5_relat_1 @ X33 @ X36)))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.54/0.76            = (k5_relat_1 @ sk_C @ X0))
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.54/0.76          | ~ (v1_funct_1 @ X0)
% 0.54/0.76          | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.76  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.54/0.76            = (k5_relat_1 @ sk_C @ X0))
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.54/0.76          | ~ (v1_funct_1 @ X0))),
% 0.54/0.76      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      ((~ (v1_funct_1 @ sk_D)
% 0.54/0.76        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.54/0.76            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['13', '18'])).
% 0.54/0.76  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('21', plain,
% 0.54/0.76      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.54/0.76        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.54/0.76        (k6_partfun1 @ sk_A))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(dt_k1_partfun1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.76     ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.76         ( v1_funct_1 @ F ) & 
% 0.54/0.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.54/0.76       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.54/0.76         ( m1_subset_1 @
% 0.54/0.76           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.54/0.76           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.54/0.76          | ~ (v1_funct_1 @ X27)
% 0.54/0.76          | ~ (v1_funct_1 @ X30)
% 0.54/0.76          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.54/0.76          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 0.54/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.54/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.54/0.76          | ~ (v1_funct_1 @ X1)
% 0.54/0.76          | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.76  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('27', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.54/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.54/0.76          | ~ (v1_funct_1 @ X1))),
% 0.54/0.76      inference('demod', [status(thm)], ['25', '26'])).
% 0.54/0.76  thf('28', plain,
% 0.54/0.76      ((~ (v1_funct_1 @ sk_D)
% 0.54/0.76        | (m1_subset_1 @ 
% 0.54/0.76           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.54/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['22', '27'])).
% 0.54/0.76  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('30', plain,
% 0.54/0.76      ((m1_subset_1 @ 
% 0.54/0.76        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.76  thf(redefinition_r2_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.54/0.76  thf('31', plain,
% 0.54/0.76      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.54/0.76          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.54/0.76          | ((X22) = (X25))
% 0.54/0.76          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.54/0.76  thf('32', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.54/0.76             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.54/0.76          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.76  thf('33', plain,
% 0.54/0.76      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.54/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.54/0.76        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.54/0.76            = (k6_partfun1 @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['21', '32'])).
% 0.54/0.76  thf(t29_relset_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( m1_subset_1 @
% 0.54/0.76       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      (![X26 : $i]:
% 0.54/0.76         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 0.54/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.54/0.76  thf(redefinition_k6_partfun1, axiom,
% 0.54/0.76    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.54/0.76  thf('35', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.76  thf('36', plain,
% 0.54/0.76      (![X26 : $i]:
% 0.54/0.76         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 0.54/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.54/0.76      inference('demod', [status(thm)], ['34', '35'])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.54/0.76         = (k6_partfun1 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['33', '36'])).
% 0.54/0.76  thf('38', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.54/0.76      inference('demod', [status(thm)], ['19', '20', '37'])).
% 0.54/0.76  thf(t27_funct_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.76           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.54/0.76             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      (![X11 : $i, X12 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X11)
% 0.54/0.76          | ~ (v1_funct_1 @ X11)
% 0.54/0.76          | (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X12))
% 0.54/0.76          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X12)) != (k1_relat_1 @ X11))
% 0.54/0.76          | ~ (v1_funct_1 @ X12)
% 0.54/0.76          | ~ (v1_relat_1 @ X12))),
% 0.54/0.76      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      ((((k1_relat_1 @ (k6_partfun1 @ sk_A)) != (k1_relat_1 @ sk_C))
% 0.54/0.76        | ~ (v1_relat_1 @ sk_D)
% 0.54/0.76        | ~ (v1_funct_1 @ sk_D)
% 0.54/0.76        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))
% 0.54/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.76        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.76  thf(t71_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.54/0.76       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.54/0.76  thf('41', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.54/0.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.54/0.76  thf('42', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.76  thf('43', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 0.54/0.76      inference('demod', [status(thm)], ['41', '42'])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(t35_funct_2, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.54/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.76           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.54/0.76             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.54/0.76  thf('45', plain,
% 0.54/0.76      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.54/0.76         (((X40) = (k1_xboole_0))
% 0.54/0.76          | ~ (v1_funct_1 @ X41)
% 0.54/0.76          | ~ (v1_funct_2 @ X41 @ X42 @ X40)
% 0.54/0.76          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 0.54/0.76          | ((k5_relat_1 @ X41 @ (k2_funct_1 @ X41)) = (k6_partfun1 @ X42))
% 0.54/0.76          | ~ (v2_funct_1 @ X41)
% 0.54/0.76          | ((k2_relset_1 @ X42 @ X40 @ X41) != (X40)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.54/0.76  thf('46', plain,
% 0.54/0.76      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.54/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.54/0.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.54/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.76  thf('47', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('49', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      ((((sk_B) != (sk_B))
% 0.54/0.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      ((((sk_B) = (k1_xboole_0))
% 0.54/0.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['51'])).
% 0.54/0.76  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.54/0.76      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.54/0.76  thf(t58_funct_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.76       ( ( v2_funct_1 @ A ) =>
% 0.54/0.76         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.54/0.76             ( k1_relat_1 @ A ) ) & 
% 0.54/0.76           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.54/0.76             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.54/0.76  thf('55', plain,
% 0.54/0.76      (![X15 : $i]:
% 0.54/0.76         (~ (v2_funct_1 @ X15)
% 0.54/0.76          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ (k2_funct_1 @ X15)))
% 0.54/0.76              = (k1_relat_1 @ X15))
% 0.54/0.76          | ~ (v1_funct_1 @ X15)
% 0.54/0.76          | ~ (v1_relat_1 @ X15))),
% 0.54/0.76      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.54/0.76  thf('56', plain,
% 0.54/0.76      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 0.54/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.76      inference('sup+', [status(thm)], ['54', '55'])).
% 0.54/0.76  thf('57', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.54/0.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.54/0.76  thf('58', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.76  thf('59', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 0.54/0.76      inference('demod', [status(thm)], ['57', '58'])).
% 0.54/0.76  thf('60', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('61', plain,
% 0.54/0.76      (![X3 : $i, X4 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.54/0.76          | (v1_relat_1 @ X3)
% 0.54/0.76          | ~ (v1_relat_1 @ X4))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.76  thf('62', plain,
% 0.54/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.76  thf('63', plain,
% 0.54/0.76      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.54/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.76  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.76  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('67', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['56', '59', '64', '65', '66'])).
% 0.54/0.76  thf('68', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.76      inference('demod', [status(thm)], ['7', '8'])).
% 0.54/0.76  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('70', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('71', plain,
% 0.54/0.76      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.54/0.76         (((X40) = (k1_xboole_0))
% 0.54/0.76          | ~ (v1_funct_1 @ X41)
% 0.54/0.76          | ~ (v1_funct_2 @ X41 @ X42 @ X40)
% 0.54/0.76          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 0.54/0.76          | ((k5_relat_1 @ (k2_funct_1 @ X41) @ X41) = (k6_partfun1 @ X40))
% 0.54/0.76          | ~ (v2_funct_1 @ X41)
% 0.54/0.76          | ((k2_relset_1 @ X42 @ X40 @ X41) != (X40)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.54/0.76  thf('72', plain,
% 0.54/0.76      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.54/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.76        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.54/0.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.54/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['70', '71'])).
% 0.54/0.76  thf('73', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('74', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('75', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('77', plain,
% 0.54/0.76      ((((sk_B) != (sk_B))
% 0.54/0.76        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.54/0.76  thf('78', plain,
% 0.54/0.76      ((((sk_B) = (k1_xboole_0))
% 0.54/0.76        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['77'])).
% 0.54/0.76  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('80', plain,
% 0.54/0.76      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.54/0.76      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.54/0.76  thf(t59_funct_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.76       ( ( v2_funct_1 @ A ) =>
% 0.54/0.76         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.54/0.76             ( k2_relat_1 @ A ) ) & 
% 0.54/0.76           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.54/0.76             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.54/0.76  thf('81', plain,
% 0.54/0.76      (![X16 : $i]:
% 0.54/0.76         (~ (v2_funct_1 @ X16)
% 0.54/0.76          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X16) @ X16))
% 0.54/0.76              = (k2_relat_1 @ X16))
% 0.54/0.76          | ~ (v1_funct_1 @ X16)
% 0.54/0.76          | ~ (v1_relat_1 @ X16))),
% 0.54/0.76      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.54/0.76  thf('82', plain,
% 0.54/0.76      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 0.54/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.76      inference('sup+', [status(thm)], ['80', '81'])).
% 0.54/0.76  thf('83', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 0.54/0.76      inference('demod', [status(thm)], ['57', '58'])).
% 0.54/0.76  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.76  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('87', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.54/0.76  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.76  thf('90', plain,
% 0.54/0.76      ((((sk_A) != (sk_A)) | (r1_tarski @ sk_B @ (k1_relat_1 @ sk_D)))),
% 0.54/0.76      inference('demod', [status(thm)],
% 0.54/0.76                ['40', '43', '67', '68', '69', '87', '88', '89'])).
% 0.54/0.76  thf('91', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_D))),
% 0.54/0.76      inference('simplify', [status(thm)], ['90'])).
% 0.54/0.76  thf('92', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.54/0.76      inference('demod', [status(thm)], ['12', '91'])).
% 0.54/0.76  thf('93', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.54/0.76      inference('demod', [status(thm)], ['19', '20', '37'])).
% 0.54/0.76  thf(t63_funct_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.76           ( ( ( v2_funct_1 @ A ) & 
% 0.54/0.76               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.54/0.76               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.54/0.76             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.54/0.76  thf('94', plain,
% 0.54/0.76      (![X17 : $i, X18 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X17)
% 0.54/0.76          | ~ (v1_funct_1 @ X17)
% 0.54/0.76          | ((X17) = (k2_funct_1 @ X18))
% 0.54/0.76          | ((k5_relat_1 @ X18 @ X17) != (k6_relat_1 @ (k1_relat_1 @ X18)))
% 0.54/0.76          | ((k2_relat_1 @ X18) != (k1_relat_1 @ X17))
% 0.54/0.76          | ~ (v2_funct_1 @ X18)
% 0.54/0.76          | ~ (v1_funct_1 @ X18)
% 0.54/0.76          | ~ (v1_relat_1 @ X18))),
% 0.54/0.76      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.54/0.76  thf('95', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.76  thf('96', plain,
% 0.54/0.76      (![X17 : $i, X18 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X17)
% 0.54/0.76          | ~ (v1_funct_1 @ X17)
% 0.54/0.76          | ((X17) = (k2_funct_1 @ X18))
% 0.54/0.76          | ((k5_relat_1 @ X18 @ X17) != (k6_partfun1 @ (k1_relat_1 @ X18)))
% 0.54/0.76          | ((k2_relat_1 @ X18) != (k1_relat_1 @ X17))
% 0.54/0.76          | ~ (v2_funct_1 @ X18)
% 0.54/0.76          | ~ (v1_funct_1 @ X18)
% 0.54/0.76          | ~ (v1_relat_1 @ X18))),
% 0.54/0.76      inference('demod', [status(thm)], ['94', '95'])).
% 0.54/0.76  thf('97', plain,
% 0.54/0.76      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.54/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.76        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.54/0.76        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.54/0.76        | ~ (v1_funct_1 @ sk_D)
% 0.54/0.76        | ~ (v1_relat_1 @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['93', '96'])).
% 0.54/0.76  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['56', '59', '64', '65', '66'])).
% 0.54/0.76  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.76  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('102', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.54/0.76  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 0.54/0.76      inference('demod', [status(thm)], ['7', '8'])).
% 0.54/0.76  thf('105', plain,
% 0.54/0.76      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.54/0.76        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.54/0.76        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.54/0.76      inference('demod', [status(thm)],
% 0.54/0.76                ['97', '98', '99', '100', '101', '102', '103', '104'])).
% 0.54/0.76  thf('106', plain,
% 0.54/0.76      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['105'])).
% 0.54/0.76  thf('107', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('108', plain, (((sk_B) != (k1_relat_1 @ sk_D))),
% 0.54/0.76      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 0.54/0.76  thf('109', plain, ($false),
% 0.54/0.76      inference('simplify_reflect-', [status(thm)], ['92', '108'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.54/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
