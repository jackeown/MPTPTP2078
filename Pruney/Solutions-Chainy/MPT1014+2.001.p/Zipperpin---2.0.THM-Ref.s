%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TKp1EwHuF0

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:45 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 596 expanded)
%              Number of leaves         :   34 ( 182 expanded)
%              Depth                    :   21
%              Number of atoms          : 1128 (14731 expanded)
%              Number of equality atoms :   59 ( 348 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t75_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B )
              & ( ( k2_relset_1 @ A @ A @ B )
                = A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B )
                & ( ( k2_relset_1 @ A @ A @ B )
                  = A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('25',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('37',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['34','35','36'])).

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

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','42','43','48','49','52'])).

thf('54',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['53'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v4_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('63',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('65',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['56','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t44_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( ( k5_relat_1 @ X9 @ X8 )
       != X9 )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k5_relat_1 @ sk_B @ X0 )
       != sk_B )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['50','51'])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ sk_B @ X0 )
       != sk_B )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
     != sk_B ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['40','41'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['56','67'])).

thf('79',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('80',plain,
    ( ( sk_A != sk_A )
    | ( sk_C
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,
    ( sk_C
    = ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('84',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['2','81','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TKp1EwHuF0
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 216 iterations in 0.138s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.36/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.59  thf(t75_funct_2, conjecture,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.59       ( ![C:$i]:
% 0.36/0.59         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.36/0.59             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.59           ( ( ( r2_relset_1 @
% 0.36/0.59                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B ) & 
% 0.36/0.59               ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.36/0.59             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i]:
% 0.36/0.59        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.36/0.59            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.59          ( ![C:$i]:
% 0.36/0.59            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.36/0.59                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.36/0.59              ( ( ( r2_relset_1 @
% 0.36/0.59                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B ) & 
% 0.36/0.59                  ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.36/0.59                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t75_funct_2])).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(redefinition_k6_partfun1, axiom,
% 0.36/0.59    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.36/0.59  thf('1', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.59  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(dt_k1_partfun1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.59         ( v1_funct_1 @ F ) & 
% 0.36/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.36/0.59       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.36/0.59         ( m1_subset_1 @
% 0.36/0.59           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.36/0.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.36/0.59          | ~ (v1_funct_1 @ X23)
% 0.36/0.59          | ~ (v1_funct_1 @ X26)
% 0.36/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.36/0.59          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.36/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.36/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.36/0.59          | ~ (v1_funct_1 @ X1)
% 0.36/0.59          | ~ (v1_funct_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.36/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.36/0.59          | ~ (v1_funct_1 @ X1))),
% 0.36/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.59        | (m1_subset_1 @ 
% 0.36/0.59           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.36/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '9'])).
% 0.36/0.59  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      ((m1_subset_1 @ 
% 0.36/0.59        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.59  thf(redefinition_k1_partfun1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.59         ( v1_funct_1 @ F ) & 
% 0.36/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.36/0.59       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.36/0.59          | ~ (v1_funct_1 @ X29)
% 0.36/0.59          | ~ (v1_funct_1 @ X32)
% 0.36/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.36/0.59          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.36/0.59              = (k5_relat_1 @ X29 @ X32)))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 0.36/0.59            (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.36/0.59            = (k5_relat_1 @ 
% 0.36/0.59               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0))
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_1 @ 
% 0.36/0.59               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.36/0.59          | ~ (v1_funct_1 @ X23)
% 0.36/0.59          | ~ (v1_funct_1 @ X26)
% 0.36/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.36/0.59          | (v1_funct_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.59          | ~ (v1_funct_1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.59        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['15', '20'])).
% 0.36/0.59  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C))),
% 0.36/0.59      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 0.36/0.59            (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.36/0.59            = (k5_relat_1 @ 
% 0.36/0.59               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0))
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.59          | ~ (v1_funct_1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['14', '23'])).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.36/0.59        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      ((m1_subset_1 @ 
% 0.36/0.59        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.59  thf(redefinition_r2_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.36/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.36/0.59          | ((X19) = (X22))
% 0.36/0.59          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.36/0.59             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.36/0.59          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.36/0.59        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (sk_B)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['25', '28'])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.59  thf('33', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.36/0.59            = (k5_relat_1 @ sk_B @ X0))
% 0.36/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.59          | ~ (v1_funct_1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['24', '31', '32'])).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.59        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.36/0.59            = (k5_relat_1 @ sk_B @ sk_C)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['3', '33'])).
% 0.36/0.59  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.59  thf('37', plain, (((sk_B) = (k5_relat_1 @ sk_B @ sk_C))),
% 0.36/0.59      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.36/0.59  thf(t27_funct_1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.59           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.36/0.59             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.36/0.59  thf('38', plain,
% 0.36/0.59      (![X6 : $i, X7 : $i]:
% 0.36/0.59         (~ (v1_relat_1 @ X6)
% 0.36/0.59          | ~ (v1_funct_1 @ X6)
% 0.36/0.59          | (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X7))
% 0.36/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X7)) != (k1_relat_1 @ X6))
% 0.36/0.59          | ~ (v1_funct_1 @ X7)
% 0.36/0.59          | ~ (v1_relat_1 @ X7))),
% 0.36/0.59      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.36/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.59        | (r1_tarski @ (k2_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C))
% 0.36/0.59        | ~ (v1_funct_1 @ sk_B)
% 0.36/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(cc1_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( v1_relat_1 @ C ) ))).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.59         ((v1_relat_1 @ X10)
% 0.36/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.59  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.59  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('44', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.59  thf('45', plain,
% 0.36/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.59         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.36/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.59  thf('47', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('48', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.36/0.59      inference('sup+', [status(thm)], ['46', '47'])).
% 0.36/0.59  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('50', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('51', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.59         ((v1_relat_1 @ X10)
% 0.36/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.59  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.59  thf('53', plain,
% 0.36/0.59      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.36/0.59        | (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.36/0.59      inference('demod', [status(thm)], ['39', '42', '43', '48', '49', '52'])).
% 0.36/0.59  thf('54', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.36/0.59      inference('simplify', [status(thm)], ['53'])).
% 0.36/0.59  thf(t12_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.59  thf('55', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i]:
% 0.36/0.59         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.59  thf('56', plain,
% 0.36/0.59      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.36/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.59  thf('57', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(cc2_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.59  thf('58', plain,
% 0.36/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.59         ((v4_relat_1 @ X13 @ X14)
% 0.36/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.59  thf('59', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.36/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.59  thf(d18_relat_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( v1_relat_1 @ B ) =>
% 0.36/0.59       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.59  thf('60', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         (~ (v4_relat_1 @ X4 @ X5)
% 0.36/0.59          | (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 0.36/0.59          | ~ (v1_relat_1 @ X4))),
% 0.36/0.59      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.59  thf('61', plain,
% 0.36/0.59      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.59  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.59  thf('63', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.36/0.59  thf('64', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i]:
% 0.36/0.59         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.59  thf('65', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.59  thf('66', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.59  thf('67', plain, (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['65', '66'])).
% 0.36/0.59  thf('68', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.36/0.59      inference('sup+', [status(thm)], ['56', '67'])).
% 0.36/0.59  thf('69', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.36/0.59      inference('sup+', [status(thm)], ['46', '47'])).
% 0.36/0.59  thf(t44_funct_1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.59           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.36/0.59               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.36/0.59             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.36/0.59  thf('70', plain,
% 0.36/0.59      (![X8 : $i, X9 : $i]:
% 0.36/0.59         (~ (v1_relat_1 @ X8)
% 0.36/0.59          | ~ (v1_funct_1 @ X8)
% 0.36/0.59          | ((X8) = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.36/0.59          | ((k5_relat_1 @ X9 @ X8) != (X9))
% 0.36/0.59          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X8))
% 0.36/0.59          | ~ (v1_funct_1 @ X9)
% 0.36/0.59          | ~ (v1_relat_1 @ X9))),
% 0.36/0.59      inference('cnf', [status(esa)], [t44_funct_1])).
% 0.36/0.59  thf('71', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((sk_A) != (k1_relat_1 @ X0))
% 0.36/0.59          | ~ (v1_relat_1 @ sk_B)
% 0.36/0.59          | ~ (v1_funct_1 @ sk_B)
% 0.36/0.59          | ((k5_relat_1 @ sk_B @ X0) != (sk_B))
% 0.36/0.59          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_relat_1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.59  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.59  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('74', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((sk_A) != (k1_relat_1 @ X0))
% 0.36/0.59          | ((k5_relat_1 @ sk_B @ X0) != (sk_B))
% 0.36/0.59          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_relat_1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.36/0.59  thf('75', plain,
% 0.36/0.59      ((((sk_A) != (sk_A))
% 0.36/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.59        | ((sk_C) = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.36/0.59        | ((k5_relat_1 @ sk_B @ sk_C) != (sk_B)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['68', '74'])).
% 0.36/0.59  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.59  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('78', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.36/0.59      inference('sup+', [status(thm)], ['56', '67'])).
% 0.36/0.59  thf('79', plain, (((sk_B) = (k5_relat_1 @ sk_B @ sk_C))),
% 0.36/0.59      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.36/0.59  thf('80', plain,
% 0.36/0.59      ((((sk_A) != (sk_A))
% 0.36/0.59        | ((sk_C) = (k6_relat_1 @ sk_A))
% 0.36/0.59        | ((sk_B) != (sk_B)))),
% 0.36/0.59      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.36/0.59  thf('81', plain, (((sk_C) = (k6_relat_1 @ sk_A))),
% 0.36/0.59      inference('simplify', [status(thm)], ['80'])).
% 0.36/0.59  thf('82', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('83', plain,
% 0.36/0.59      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.36/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.36/0.59          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 0.36/0.59          | ((X19) != (X22)))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.36/0.59  thf('84', plain,
% 0.36/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.59         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.36/0.59          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.36/0.59      inference('simplify', [status(thm)], ['83'])).
% 0.36/0.59  thf('85', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.36/0.59      inference('sup-', [status(thm)], ['82', '84'])).
% 0.36/0.59  thf('86', plain, ($false),
% 0.36/0.59      inference('demod', [status(thm)], ['2', '81', '85'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
