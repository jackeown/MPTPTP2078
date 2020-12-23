%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BsGf2vtMKo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:53 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 208 expanded)
%              Number of leaves         :   35 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  857 (3818 expanded)
%              Number of equality atoms :   39 ( 125 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t24_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
             => ( ( k2_relset_1 @ A @ B @ C )
                = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_funct_2])).

thf('0',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ X0 )
      | ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k5_relat_1 @ sk_D @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['17','22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('26',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('35',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','42'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('47',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['33','36','45','46','47','52','57'])).

thf('59',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('61',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BsGf2vtMKo
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.89/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.09  % Solved by: fo/fo7.sh
% 0.89/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.09  % done 743 iterations in 0.637s
% 0.89/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.09  % SZS output start Refutation
% 0.89/1.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.09  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.89/1.09  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.89/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.09  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.89/1.09  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.09  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.89/1.09  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.09  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.09  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.89/1.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.09  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.09  thf(t24_funct_2, conjecture,
% 0.89/1.09    (![A:$i,B:$i,C:$i]:
% 0.89/1.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.09       ( ![D:$i]:
% 0.89/1.09         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.09             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.09           ( ( r2_relset_1 @
% 0.89/1.09               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.89/1.09               ( k6_partfun1 @ B ) ) =>
% 0.89/1.09             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.89/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.09    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.09        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.09            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.09          ( ![D:$i]:
% 0.89/1.09            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.09                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.09              ( ( r2_relset_1 @
% 0.89/1.09                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.89/1.09                  ( k6_partfun1 @ B ) ) =>
% 0.89/1.09                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.89/1.09    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.89/1.09  thf('0', plain,
% 0.89/1.09      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.89/1.09        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.89/1.09        (k6_partfun1 @ sk_B))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('1', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('2', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(redefinition_k1_partfun1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.09     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.09         ( v1_funct_1 @ F ) & 
% 0.89/1.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.09       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.89/1.09  thf('3', plain,
% 0.89/1.09      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.89/1.09          | ~ (v1_funct_1 @ X37)
% 0.89/1.09          | ~ (v1_funct_1 @ X40)
% 0.89/1.09          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.89/1.09          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 0.89/1.09              = (k5_relat_1 @ X37 @ X40)))),
% 0.89/1.09      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.89/1.09  thf('4', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.89/1.09            = (k5_relat_1 @ sk_D @ X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ sk_D))),
% 0.89/1.09      inference('sup-', [status(thm)], ['2', '3'])).
% 0.89/1.09  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('6', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.89/1.09            = (k5_relat_1 @ sk_D @ X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.09          | ~ (v1_funct_1 @ X0))),
% 0.89/1.09      inference('demod', [status(thm)], ['4', '5'])).
% 0.89/1.09  thf('7', plain,
% 0.89/1.09      ((~ (v1_funct_1 @ sk_C)
% 0.89/1.09        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.89/1.09            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['1', '6'])).
% 0.89/1.09  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('9', plain,
% 0.89/1.09      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.89/1.09         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.89/1.09      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.09  thf('10', plain,
% 0.89/1.09      ((r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 0.89/1.09        (k6_partfun1 @ sk_B))),
% 0.89/1.09      inference('demod', [status(thm)], ['0', '9'])).
% 0.89/1.09  thf('11', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('12', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(dt_k4_relset_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.09     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.09       ( m1_subset_1 @
% 0.89/1.09         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.89/1.09         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.89/1.09  thf('13', plain,
% 0.89/1.09      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.89/1.09          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.89/1.09          | (m1_subset_1 @ (k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 0.89/1.09             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.89/1.09  thf('14', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         ((m1_subset_1 @ (k4_relset_1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.89/1.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.89/1.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.09  thf('15', plain,
% 0.89/1.09      ((m1_subset_1 @ 
% 0.89/1.09        (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.89/1.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['11', '14'])).
% 0.89/1.09  thf(redefinition_r2_relset_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.09     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.09       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.89/1.09  thf('16', plain,
% 0.89/1.09      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.89/1.09          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.89/1.09          | ((X32) = (X35))
% 0.89/1.09          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 0.89/1.09      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.89/1.09  thf('17', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (r2_relset_1 @ sk_B @ sk_B @ 
% 0.89/1.09             (k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ X0)
% 0.89/1.09          | ((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) = (X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['15', '16'])).
% 0.89/1.09  thf('18', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('19', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(redefinition_k4_relset_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.09     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.09       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.89/1.09  thf('20', plain,
% 0.89/1.09      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.89/1.09          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.89/1.09          | ((k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 0.89/1.09              = (k5_relat_1 @ X26 @ X29)))),
% 0.89/1.09      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.89/1.09  thf('21', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (((k4_relset_1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.89/1.09            = (k5_relat_1 @ sk_D @ X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.09  thf('22', plain,
% 0.89/1.09      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.89/1.09         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['18', '21'])).
% 0.89/1.09  thf('23', plain,
% 0.89/1.09      (((k4_relset_1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.89/1.10         = (k5_relat_1 @ sk_D @ sk_C))),
% 0.89/1.10      inference('sup-', [status(thm)], ['18', '21'])).
% 0.89/1.10  thf('24', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (r2_relset_1 @ sk_B @ sk_B @ (k5_relat_1 @ sk_D @ sk_C) @ X0)
% 0.89/1.10          | ((k5_relat_1 @ sk_D @ sk_C) = (X0))
% 0.89/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.89/1.10      inference('demod', [status(thm)], ['17', '22', '23'])).
% 0.89/1.10  thf('25', plain,
% 0.89/1.10      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_B) @ 
% 0.89/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.89/1.10        | ((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['10', '24'])).
% 0.89/1.10  thf(t29_relset_1, axiom,
% 0.89/1.10    (![A:$i]:
% 0.89/1.10     ( m1_subset_1 @
% 0.89/1.10       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.89/1.10  thf('26', plain,
% 0.89/1.10      (![X36 : $i]:
% 0.89/1.10         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 0.89/1.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.89/1.10  thf(redefinition_k6_partfun1, axiom,
% 0.89/1.10    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.89/1.10  thf('27', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.89/1.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.10  thf('28', plain,
% 0.89/1.10      (![X36 : $i]:
% 0.89/1.10         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.89/1.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.89/1.10      inference('demod', [status(thm)], ['26', '27'])).
% 0.89/1.10  thf('29', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.89/1.10      inference('demod', [status(thm)], ['25', '28'])).
% 0.89/1.10  thf(t45_relat_1, axiom,
% 0.89/1.10    (![A:$i]:
% 0.89/1.10     ( ( v1_relat_1 @ A ) =>
% 0.89/1.10       ( ![B:$i]:
% 0.89/1.10         ( ( v1_relat_1 @ B ) =>
% 0.89/1.10           ( r1_tarski @
% 0.89/1.10             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.89/1.10  thf('30', plain,
% 0.89/1.10      (![X10 : $i, X11 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X10)
% 0.89/1.10          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.89/1.10             (k2_relat_1 @ X10))
% 0.89/1.10          | ~ (v1_relat_1 @ X11))),
% 0.89/1.10      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.89/1.10  thf(d10_xboole_0, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.10  thf('31', plain,
% 0.89/1.10      (![X0 : $i, X2 : $i]:
% 0.89/1.10         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.10  thf('32', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X1)
% 0.89/1.10          | ~ (v1_relat_1 @ X0)
% 0.89/1.10          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.89/1.10               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.89/1.10          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.89/1.10      inference('sup-', [status(thm)], ['30', '31'])).
% 0.89/1.10  thf('33', plain,
% 0.89/1.10      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.89/1.10           (k2_relat_1 @ (k6_partfun1 @ sk_B)))
% 0.89/1.10        | ((k2_relat_1 @ sk_C) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_C)))
% 0.89/1.10        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.10        | ~ (v1_relat_1 @ sk_D))),
% 0.89/1.10      inference('sup-', [status(thm)], ['29', '32'])).
% 0.89/1.10  thf(t71_relat_1, axiom,
% 0.89/1.10    (![A:$i]:
% 0.89/1.10     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.10       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.10  thf('34', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.89/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.10  thf('35', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.89/1.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.10  thf('36', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 0.89/1.10      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.10  thf('37', plain,
% 0.89/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(dt_k2_relset_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.10       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.89/1.10  thf('38', plain,
% 0.89/1.10      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.89/1.10         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.89/1.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.89/1.10      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.89/1.10  thf('39', plain,
% 0.89/1.10      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.89/1.10      inference('sup-', [status(thm)], ['37', '38'])).
% 0.89/1.10  thf('40', plain,
% 0.89/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(redefinition_k2_relset_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.89/1.10  thf('41', plain,
% 0.89/1.10      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.10         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.89/1.10          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.89/1.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.10  thf('42', plain,
% 0.89/1.10      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.89/1.10      inference('sup-', [status(thm)], ['40', '41'])).
% 0.89/1.10  thf('43', plain,
% 0.89/1.10      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.89/1.10      inference('demod', [status(thm)], ['39', '42'])).
% 0.89/1.10  thf(t3_subset, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.89/1.10  thf('44', plain,
% 0.89/1.10      (![X3 : $i, X4 : $i]:
% 0.89/1.10         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.89/1.10  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.89/1.10      inference('sup-', [status(thm)], ['43', '44'])).
% 0.89/1.10  thf('46', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.89/1.10      inference('demod', [status(thm)], ['25', '28'])).
% 0.89/1.10  thf('47', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 0.89/1.10      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.10  thf('48', plain,
% 0.89/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(cc2_relat_1, axiom,
% 0.89/1.10    (![A:$i]:
% 0.89/1.10     ( ( v1_relat_1 @ A ) =>
% 0.89/1.10       ( ![B:$i]:
% 0.89/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.89/1.10  thf('49', plain,
% 0.89/1.10      (![X6 : $i, X7 : $i]:
% 0.89/1.10         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.89/1.10          | (v1_relat_1 @ X6)
% 0.89/1.10          | ~ (v1_relat_1 @ X7))),
% 0.89/1.10      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.89/1.10  thf('50', plain,
% 0.89/1.10      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.89/1.10      inference('sup-', [status(thm)], ['48', '49'])).
% 0.89/1.10  thf(fc6_relat_1, axiom,
% 0.89/1.10    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.10  thf('51', plain,
% 0.89/1.10      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.89/1.10      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.10  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.10      inference('demod', [status(thm)], ['50', '51'])).
% 0.89/1.10  thf('53', plain,
% 0.89/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('54', plain,
% 0.89/1.10      (![X6 : $i, X7 : $i]:
% 0.89/1.10         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.89/1.10          | (v1_relat_1 @ X6)
% 0.89/1.10          | ~ (v1_relat_1 @ X7))),
% 0.89/1.10      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.89/1.10  thf('55', plain,
% 0.89/1.10      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.89/1.10      inference('sup-', [status(thm)], ['53', '54'])).
% 0.89/1.10  thf('56', plain,
% 0.89/1.10      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.89/1.10      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.10  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.10      inference('demod', [status(thm)], ['55', '56'])).
% 0.89/1.10  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.10      inference('demod', [status(thm)],
% 0.89/1.10                ['33', '36', '45', '46', '47', '52', '57'])).
% 0.89/1.10  thf('59', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('60', plain,
% 0.89/1.10      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.89/1.10      inference('sup-', [status(thm)], ['40', '41'])).
% 0.89/1.10  thf('61', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.89/1.10      inference('demod', [status(thm)], ['59', '60'])).
% 0.89/1.10  thf('62', plain, ($false),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 0.89/1.10  
% 0.89/1.10  % SZS output end Refutation
% 0.89/1.10  
% 0.89/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
