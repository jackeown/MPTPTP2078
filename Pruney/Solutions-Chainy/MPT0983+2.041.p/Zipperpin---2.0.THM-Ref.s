%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bGlgAAaavp

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:07 EST 2020

% Result     : Theorem 4.86s
% Output     : Refutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 480 expanded)
%              Number of leaves         :   43 ( 152 expanded)
%              Depth                    :   18
%              Number of atoms          : 1260 (9403 expanded)
%              Number of equality atoms :   48 ( 116 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
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

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','21'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['26','29','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','21'])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('42',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('44',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('45',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('46',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('49',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('50',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('51',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('53',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('54',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['27','28'])).

thf('62',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','52','55','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
       != X27 )
      | ( v2_funct_2 @ X28 @ X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('71',plain,(
    ! [X28: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) )
      | ( v2_funct_2 @ X28 @ ( k2_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['65','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['27','28'])).

thf('76',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( $false
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['1','76'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('81',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('82',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('85',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('86',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','87'])).

thf('89',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('92',plain,(
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

thf('93',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X45 @ X43 @ X43 @ X44 @ X46 @ X42 ) )
      | ( v2_funct_1 @ X46 )
      | ( X44 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X43 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('104',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('105',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('109',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X21 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['90','113'])).

thf('115',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('116',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['77','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bGlgAAaavp
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.86/5.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.86/5.09  % Solved by: fo/fo7.sh
% 4.86/5.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.86/5.09  % done 4106 iterations in 4.632s
% 4.86/5.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.86/5.09  % SZS output start Refutation
% 4.86/5.09  thf(sk_B_type, type, sk_B: $i).
% 4.86/5.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.86/5.09  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.86/5.09  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.86/5.09  thf(sk_D_type, type, sk_D: $i).
% 4.86/5.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.86/5.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.86/5.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.86/5.09  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.86/5.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.86/5.09  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.86/5.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.86/5.09  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.86/5.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.86/5.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.86/5.09  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.86/5.09  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.86/5.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.86/5.09  thf(sk_A_type, type, sk_A: $i).
% 4.86/5.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.86/5.09  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.86/5.09  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.86/5.09  thf(sk_C_type, type, sk_C: $i).
% 4.86/5.09  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.86/5.09  thf(t29_funct_2, conjecture,
% 4.86/5.09    (![A:$i,B:$i,C:$i]:
% 4.86/5.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.86/5.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.09       ( ![D:$i]:
% 4.86/5.09         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.86/5.09             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.86/5.09           ( ( r2_relset_1 @
% 4.86/5.09               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.86/5.09               ( k6_partfun1 @ A ) ) =>
% 4.86/5.09             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.86/5.09  thf(zf_stmt_0, negated_conjecture,
% 4.86/5.09    (~( ![A:$i,B:$i,C:$i]:
% 4.86/5.09        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.86/5.09            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.09          ( ![D:$i]:
% 4.86/5.09            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.86/5.09                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.86/5.09              ( ( r2_relset_1 @
% 4.86/5.09                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.86/5.09                  ( k6_partfun1 @ A ) ) =>
% 4.86/5.09                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.86/5.09    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.86/5.09  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('1', plain,
% 4.86/5.09      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.86/5.09      inference('split', [status(esa)], ['0'])).
% 4.86/5.09  thf('2', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('3', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf(dt_k1_partfun1, axiom,
% 4.86/5.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.86/5.09     ( ( ( v1_funct_1 @ E ) & 
% 4.86/5.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.86/5.09         ( v1_funct_1 @ F ) & 
% 4.86/5.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.86/5.09       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.86/5.09         ( m1_subset_1 @
% 4.86/5.09           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.86/5.09           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.86/5.09  thf('4', plain,
% 4.86/5.09      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 4.86/5.09         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 4.86/5.09          | ~ (v1_funct_1 @ X29)
% 4.86/5.09          | ~ (v1_funct_1 @ X32)
% 4.86/5.09          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 4.86/5.09          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 4.86/5.09             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 4.86/5.09      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.86/5.09  thf('5', plain,
% 4.86/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.09         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.86/5.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.86/5.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.86/5.09          | ~ (v1_funct_1 @ X1)
% 4.86/5.09          | ~ (v1_funct_1 @ sk_C))),
% 4.86/5.09      inference('sup-', [status(thm)], ['3', '4'])).
% 4.86/5.09  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('7', plain,
% 4.86/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.09         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.86/5.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.86/5.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.86/5.09          | ~ (v1_funct_1 @ X1))),
% 4.86/5.09      inference('demod', [status(thm)], ['5', '6'])).
% 4.86/5.09  thf('8', plain,
% 4.86/5.09      ((~ (v1_funct_1 @ sk_D)
% 4.86/5.09        | (m1_subset_1 @ 
% 4.86/5.09           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.86/5.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.86/5.09      inference('sup-', [status(thm)], ['2', '7'])).
% 4.86/5.09  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('10', plain,
% 4.86/5.09      ((m1_subset_1 @ 
% 4.86/5.09        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.86/5.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.86/5.09      inference('demod', [status(thm)], ['8', '9'])).
% 4.86/5.09  thf(cc1_relset_1, axiom,
% 4.86/5.09    (![A:$i,B:$i,C:$i]:
% 4.86/5.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.86/5.09       ( v1_relat_1 @ C ) ))).
% 4.86/5.09  thf('11', plain,
% 4.86/5.09      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.86/5.09         ((v1_relat_1 @ X13)
% 4.86/5.09          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 4.86/5.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.86/5.09  thf('12', plain,
% 4.86/5.09      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 4.86/5.09      inference('sup-', [status(thm)], ['10', '11'])).
% 4.86/5.09  thf('13', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('14', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf(redefinition_k1_partfun1, axiom,
% 4.86/5.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.86/5.09     ( ( ( v1_funct_1 @ E ) & 
% 4.86/5.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.86/5.09         ( v1_funct_1 @ F ) & 
% 4.86/5.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.86/5.09       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.86/5.09  thf('15', plain,
% 4.86/5.09      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 4.86/5.09         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 4.86/5.09          | ~ (v1_funct_1 @ X35)
% 4.86/5.09          | ~ (v1_funct_1 @ X38)
% 4.86/5.09          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 4.86/5.09          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 4.86/5.09              = (k5_relat_1 @ X35 @ X38)))),
% 4.86/5.09      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.86/5.09  thf('16', plain,
% 4.86/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.09         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.86/5.09            = (k5_relat_1 @ sk_C @ X0))
% 4.86/5.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.86/5.09          | ~ (v1_funct_1 @ X0)
% 4.86/5.09          | ~ (v1_funct_1 @ sk_C))),
% 4.86/5.09      inference('sup-', [status(thm)], ['14', '15'])).
% 4.86/5.09  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('18', plain,
% 4.86/5.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.09         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.86/5.09            = (k5_relat_1 @ sk_C @ X0))
% 4.86/5.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.86/5.09          | ~ (v1_funct_1 @ X0))),
% 4.86/5.09      inference('demod', [status(thm)], ['16', '17'])).
% 4.86/5.09  thf('19', plain,
% 4.86/5.09      ((~ (v1_funct_1 @ sk_D)
% 4.86/5.09        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.86/5.09            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.86/5.09      inference('sup-', [status(thm)], ['13', '18'])).
% 4.86/5.09  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('21', plain,
% 4.86/5.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.86/5.09         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.86/5.09      inference('demod', [status(thm)], ['19', '20'])).
% 4.86/5.09  thf('22', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 4.86/5.09      inference('demod', [status(thm)], ['12', '21'])).
% 4.86/5.09  thf(t45_relat_1, axiom,
% 4.86/5.09    (![A:$i]:
% 4.86/5.09     ( ( v1_relat_1 @ A ) =>
% 4.86/5.09       ( ![B:$i]:
% 4.86/5.09         ( ( v1_relat_1 @ B ) =>
% 4.86/5.09           ( r1_tarski @
% 4.86/5.09             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 4.86/5.09  thf('23', plain,
% 4.86/5.09      (![X7 : $i, X8 : $i]:
% 4.86/5.09         (~ (v1_relat_1 @ X7)
% 4.86/5.09          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 4.86/5.09             (k2_relat_1 @ X7))
% 4.86/5.09          | ~ (v1_relat_1 @ X8))),
% 4.86/5.09      inference('cnf', [status(esa)], [t45_relat_1])).
% 4.86/5.09  thf(d19_relat_1, axiom,
% 4.86/5.09    (![A:$i,B:$i]:
% 4.86/5.09     ( ( v1_relat_1 @ B ) =>
% 4.86/5.09       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.86/5.09  thf('24', plain,
% 4.86/5.09      (![X5 : $i, X6 : $i]:
% 4.86/5.09         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 4.86/5.09          | (v5_relat_1 @ X5 @ X6)
% 4.86/5.09          | ~ (v1_relat_1 @ X5))),
% 4.86/5.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.86/5.09  thf('25', plain,
% 4.86/5.09      (![X0 : $i, X1 : $i]:
% 4.86/5.09         (~ (v1_relat_1 @ X1)
% 4.86/5.09          | ~ (v1_relat_1 @ X0)
% 4.86/5.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 4.86/5.09          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 4.86/5.09      inference('sup-', [status(thm)], ['23', '24'])).
% 4.86/5.09  thf('26', plain,
% 4.86/5.09      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 4.86/5.09        | ~ (v1_relat_1 @ sk_D)
% 4.86/5.09        | ~ (v1_relat_1 @ sk_C))),
% 4.86/5.09      inference('sup-', [status(thm)], ['22', '25'])).
% 4.86/5.09  thf('27', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('28', plain,
% 4.86/5.09      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.86/5.09         ((v1_relat_1 @ X13)
% 4.86/5.09          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 4.86/5.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.86/5.09  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 4.86/5.09      inference('sup-', [status(thm)], ['27', '28'])).
% 4.86/5.09  thf('30', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('31', plain,
% 4.86/5.09      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.86/5.09         ((v1_relat_1 @ X13)
% 4.86/5.09          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 4.86/5.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.86/5.09  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 4.86/5.09      inference('sup-', [status(thm)], ['30', '31'])).
% 4.86/5.09  thf('33', plain,
% 4.86/5.09      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 4.86/5.09      inference('demod', [status(thm)], ['26', '29', '32'])).
% 4.86/5.09  thf('34', plain,
% 4.86/5.09      (![X5 : $i, X6 : $i]:
% 4.86/5.09         (~ (v5_relat_1 @ X5 @ X6)
% 4.86/5.09          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 4.86/5.09          | ~ (v1_relat_1 @ X5))),
% 4.86/5.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.86/5.09  thf('35', plain,
% 4.86/5.09      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.86/5.09        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 4.86/5.09           (k2_relat_1 @ sk_D)))),
% 4.86/5.09      inference('sup-', [status(thm)], ['33', '34'])).
% 4.86/5.09  thf('36', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 4.86/5.09      inference('demod', [status(thm)], ['12', '21'])).
% 4.86/5.09  thf('37', plain,
% 4.86/5.09      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 4.86/5.09        (k2_relat_1 @ sk_D))),
% 4.86/5.09      inference('demod', [status(thm)], ['35', '36'])).
% 4.86/5.09  thf(d10_xboole_0, axiom,
% 4.86/5.09    (![A:$i,B:$i]:
% 4.86/5.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.86/5.09  thf('38', plain,
% 4.86/5.09      (![X0 : $i, X2 : $i]:
% 4.86/5.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.86/5.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.86/5.09  thf('39', plain,
% 4.86/5.09      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 4.86/5.09           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 4.86/5.09        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 4.86/5.09      inference('sup-', [status(thm)], ['37', '38'])).
% 4.86/5.09  thf('40', plain,
% 4.86/5.09      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.86/5.09        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.86/5.09        (k6_partfun1 @ sk_A))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('41', plain,
% 4.86/5.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.86/5.09         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.86/5.09      inference('demod', [status(thm)], ['19', '20'])).
% 4.86/5.09  thf('42', plain,
% 4.86/5.09      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.86/5.09        (k6_partfun1 @ sk_A))),
% 4.86/5.09      inference('demod', [status(thm)], ['40', '41'])).
% 4.86/5.09  thf('43', plain,
% 4.86/5.09      ((m1_subset_1 @ 
% 4.86/5.09        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.86/5.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.86/5.09      inference('demod', [status(thm)], ['8', '9'])).
% 4.86/5.09  thf('44', plain,
% 4.86/5.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.86/5.09         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.86/5.09      inference('demod', [status(thm)], ['19', '20'])).
% 4.86/5.09  thf('45', plain,
% 4.86/5.09      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.86/5.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.86/5.09      inference('demod', [status(thm)], ['43', '44'])).
% 4.86/5.09  thf(redefinition_r2_relset_1, axiom,
% 4.86/5.09    (![A:$i,B:$i,C:$i,D:$i]:
% 4.86/5.09     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.86/5.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.09       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.86/5.09  thf('46', plain,
% 4.86/5.09      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 4.86/5.09         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 4.86/5.09          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 4.86/5.09          | ((X22) = (X25))
% 4.86/5.09          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 4.86/5.09      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.86/5.09  thf('47', plain,
% 4.86/5.09      (![X0 : $i]:
% 4.86/5.09         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 4.86/5.09          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 4.86/5.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.86/5.09      inference('sup-', [status(thm)], ['45', '46'])).
% 4.86/5.09  thf('48', plain,
% 4.86/5.09      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.86/5.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.86/5.09        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 4.86/5.09      inference('sup-', [status(thm)], ['42', '47'])).
% 4.86/5.09  thf(t29_relset_1, axiom,
% 4.86/5.09    (![A:$i]:
% 4.86/5.09     ( m1_subset_1 @
% 4.86/5.09       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.86/5.09  thf('49', plain,
% 4.86/5.09      (![X26 : $i]:
% 4.86/5.09         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 4.86/5.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 4.86/5.09      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.86/5.09  thf(redefinition_k6_partfun1, axiom,
% 4.86/5.09    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.86/5.09  thf('50', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 4.86/5.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.86/5.09  thf('51', plain,
% 4.86/5.09      (![X26 : $i]:
% 4.86/5.09         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 4.86/5.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 4.86/5.09      inference('demod', [status(thm)], ['49', '50'])).
% 4.86/5.09  thf('52', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.86/5.09      inference('demod', [status(thm)], ['48', '51'])).
% 4.86/5.09  thf(t71_relat_1, axiom,
% 4.86/5.09    (![A:$i]:
% 4.86/5.09     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.86/5.09       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.86/5.09  thf('53', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 4.86/5.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.86/5.09  thf('54', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 4.86/5.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.86/5.09  thf('55', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 4.86/5.09      inference('demod', [status(thm)], ['53', '54'])).
% 4.86/5.09  thf('56', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf(cc2_relset_1, axiom,
% 4.86/5.09    (![A:$i,B:$i,C:$i]:
% 4.86/5.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.86/5.09       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.86/5.09  thf('57', plain,
% 4.86/5.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.86/5.09         ((v5_relat_1 @ X16 @ X18)
% 4.86/5.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 4.86/5.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.86/5.09  thf('58', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.86/5.09      inference('sup-', [status(thm)], ['56', '57'])).
% 4.86/5.09  thf('59', plain,
% 4.86/5.09      (![X5 : $i, X6 : $i]:
% 4.86/5.09         (~ (v5_relat_1 @ X5 @ X6)
% 4.86/5.09          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 4.86/5.09          | ~ (v1_relat_1 @ X5))),
% 4.86/5.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.86/5.09  thf('60', plain,
% 4.86/5.09      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 4.86/5.09      inference('sup-', [status(thm)], ['58', '59'])).
% 4.86/5.09  thf('61', plain, ((v1_relat_1 @ sk_D)),
% 4.86/5.09      inference('sup-', [status(thm)], ['27', '28'])).
% 4.86/5.09  thf('62', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 4.86/5.09      inference('demod', [status(thm)], ['60', '61'])).
% 4.86/5.09  thf('63', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.86/5.09      inference('demod', [status(thm)], ['48', '51'])).
% 4.86/5.09  thf('64', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 4.86/5.09      inference('demod', [status(thm)], ['53', '54'])).
% 4.86/5.09  thf('65', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.86/5.09      inference('demod', [status(thm)], ['39', '52', '55', '62', '63', '64'])).
% 4.86/5.09  thf('66', plain,
% 4.86/5.09      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.86/5.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.86/5.09  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.86/5.09      inference('simplify', [status(thm)], ['66'])).
% 4.86/5.09  thf('68', plain,
% 4.86/5.09      (![X5 : $i, X6 : $i]:
% 4.86/5.09         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 4.86/5.09          | (v5_relat_1 @ X5 @ X6)
% 4.86/5.09          | ~ (v1_relat_1 @ X5))),
% 4.86/5.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.86/5.09  thf('69', plain,
% 4.86/5.09      (![X0 : $i]:
% 4.86/5.09         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.86/5.09      inference('sup-', [status(thm)], ['67', '68'])).
% 4.86/5.09  thf(d3_funct_2, axiom,
% 4.86/5.09    (![A:$i,B:$i]:
% 4.86/5.09     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.86/5.09       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.86/5.09  thf('70', plain,
% 4.86/5.09      (![X27 : $i, X28 : $i]:
% 4.86/5.09         (((k2_relat_1 @ X28) != (X27))
% 4.86/5.09          | (v2_funct_2 @ X28 @ X27)
% 4.86/5.09          | ~ (v5_relat_1 @ X28 @ X27)
% 4.86/5.09          | ~ (v1_relat_1 @ X28))),
% 4.86/5.09      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.86/5.09  thf('71', plain,
% 4.86/5.09      (![X28 : $i]:
% 4.86/5.09         (~ (v1_relat_1 @ X28)
% 4.86/5.09          | ~ (v5_relat_1 @ X28 @ (k2_relat_1 @ X28))
% 4.86/5.09          | (v2_funct_2 @ X28 @ (k2_relat_1 @ X28)))),
% 4.86/5.09      inference('simplify', [status(thm)], ['70'])).
% 4.86/5.09  thf('72', plain,
% 4.86/5.09      (![X0 : $i]:
% 4.86/5.09         (~ (v1_relat_1 @ X0)
% 4.86/5.09          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.86/5.09          | ~ (v1_relat_1 @ X0))),
% 4.86/5.09      inference('sup-', [status(thm)], ['69', '71'])).
% 4.86/5.09  thf('73', plain,
% 4.86/5.09      (![X0 : $i]:
% 4.86/5.09         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.86/5.09      inference('simplify', [status(thm)], ['72'])).
% 4.86/5.09  thf('74', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.86/5.09      inference('sup+', [status(thm)], ['65', '73'])).
% 4.86/5.09  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 4.86/5.09      inference('sup-', [status(thm)], ['27', '28'])).
% 4.86/5.09  thf('76', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.86/5.09      inference('demod', [status(thm)], ['74', '75'])).
% 4.86/5.09  thf('77', plain, (($false) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.86/5.09      inference('demod', [status(thm)], ['1', '76'])).
% 4.86/5.09  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.86/5.09  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.86/5.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.86/5.09  thf(t8_boole, axiom,
% 4.86/5.09    (![A:$i,B:$i]:
% 4.86/5.09     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.86/5.09  thf('79', plain,
% 4.86/5.09      (![X3 : $i, X4 : $i]:
% 4.86/5.09         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 4.86/5.09      inference('cnf', [status(esa)], [t8_boole])).
% 4.86/5.09  thf('80', plain,
% 4.86/5.09      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.86/5.09      inference('sup-', [status(thm)], ['78', '79'])).
% 4.86/5.09  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 4.86/5.09  thf('81', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.86/5.09      inference('cnf', [status(esa)], [t81_relat_1])).
% 4.86/5.09  thf('82', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 4.86/5.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.86/5.09  thf('83', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.86/5.09      inference('demod', [status(thm)], ['81', '82'])).
% 4.86/5.09  thf(fc4_funct_1, axiom,
% 4.86/5.09    (![A:$i]:
% 4.86/5.09     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.86/5.09       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.86/5.09  thf('84', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 4.86/5.09      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.86/5.09  thf('85', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 4.86/5.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.86/5.09  thf('86', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 4.86/5.09      inference('demod', [status(thm)], ['84', '85'])).
% 4.86/5.09  thf('87', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.86/5.09      inference('sup+', [status(thm)], ['83', '86'])).
% 4.86/5.09  thf('88', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 4.86/5.09      inference('sup+', [status(thm)], ['80', '87'])).
% 4.86/5.09  thf('89', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.86/5.09      inference('split', [status(esa)], ['0'])).
% 4.86/5.09  thf('90', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.86/5.09      inference('sup-', [status(thm)], ['88', '89'])).
% 4.86/5.09  thf('91', plain,
% 4.86/5.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.86/5.09         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.86/5.09      inference('demod', [status(thm)], ['19', '20'])).
% 4.86/5.09  thf('92', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf(t26_funct_2, axiom,
% 4.86/5.09    (![A:$i,B:$i,C:$i,D:$i]:
% 4.86/5.09     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.86/5.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.86/5.09       ( ![E:$i]:
% 4.86/5.09         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.86/5.09             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.86/5.09           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.86/5.09             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.86/5.09               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.86/5.09  thf('93', plain,
% 4.86/5.09      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.86/5.09         (~ (v1_funct_1 @ X42)
% 4.86/5.09          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 4.86/5.09          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 4.86/5.09          | ~ (v2_funct_1 @ (k1_partfun1 @ X45 @ X43 @ X43 @ X44 @ X46 @ X42))
% 4.86/5.09          | (v2_funct_1 @ X46)
% 4.86/5.09          | ((X44) = (k1_xboole_0))
% 4.86/5.09          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X43)))
% 4.86/5.09          | ~ (v1_funct_2 @ X46 @ X45 @ X43)
% 4.86/5.09          | ~ (v1_funct_1 @ X46))),
% 4.86/5.09      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.86/5.09  thf('94', plain,
% 4.86/5.09      (![X0 : $i, X1 : $i]:
% 4.86/5.09         (~ (v1_funct_1 @ X0)
% 4.86/5.09          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.86/5.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.86/5.09          | ((sk_A) = (k1_xboole_0))
% 4.86/5.09          | (v2_funct_1 @ X0)
% 4.86/5.09          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.86/5.09          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.86/5.09          | ~ (v1_funct_1 @ sk_D))),
% 4.86/5.09      inference('sup-', [status(thm)], ['92', '93'])).
% 4.86/5.09  thf('95', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('97', plain,
% 4.86/5.09      (![X0 : $i, X1 : $i]:
% 4.86/5.09         (~ (v1_funct_1 @ X0)
% 4.86/5.09          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.86/5.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.86/5.09          | ((sk_A) = (k1_xboole_0))
% 4.86/5.09          | (v2_funct_1 @ X0)
% 4.86/5.09          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.86/5.09      inference('demod', [status(thm)], ['94', '95', '96'])).
% 4.86/5.09  thf('98', plain,
% 4.86/5.09      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.86/5.09        | (v2_funct_1 @ sk_C)
% 4.86/5.09        | ((sk_A) = (k1_xboole_0))
% 4.86/5.09        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.86/5.09        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.86/5.09        | ~ (v1_funct_1 @ sk_C))),
% 4.86/5.09      inference('sup-', [status(thm)], ['91', '97'])).
% 4.86/5.09  thf('99', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('100', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf('102', plain,
% 4.86/5.09      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.86/5.09        | (v2_funct_1 @ sk_C)
% 4.86/5.09        | ((sk_A) = (k1_xboole_0)))),
% 4.86/5.09      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 4.86/5.09  thf('103', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.86/5.09      inference('demod', [status(thm)], ['48', '51'])).
% 4.86/5.09  thf('104', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 4.86/5.09      inference('demod', [status(thm)], ['84', '85'])).
% 4.86/5.09  thf('105', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.86/5.09      inference('demod', [status(thm)], ['102', '103', '104'])).
% 4.86/5.09  thf('106', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.86/5.09      inference('split', [status(esa)], ['0'])).
% 4.86/5.09  thf('107', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.86/5.09      inference('sup-', [status(thm)], ['105', '106'])).
% 4.86/5.09  thf('108', plain,
% 4.86/5.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.86/5.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.86/5.09  thf(cc3_relset_1, axiom,
% 4.86/5.09    (![A:$i,B:$i]:
% 4.86/5.09     ( ( v1_xboole_0 @ A ) =>
% 4.86/5.09       ( ![C:$i]:
% 4.86/5.09         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.86/5.09           ( v1_xboole_0 @ C ) ) ) ))).
% 4.86/5.09  thf('109', plain,
% 4.86/5.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.86/5.09         (~ (v1_xboole_0 @ X19)
% 4.86/5.09          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X21)))
% 4.86/5.09          | (v1_xboole_0 @ X20))),
% 4.86/5.09      inference('cnf', [status(esa)], [cc3_relset_1])).
% 4.86/5.09  thf('110', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 4.86/5.09      inference('sup-', [status(thm)], ['108', '109'])).
% 4.86/5.09  thf('111', plain,
% 4.86/5.09      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 4.86/5.09         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.86/5.09      inference('sup-', [status(thm)], ['107', '110'])).
% 4.86/5.09  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.86/5.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.86/5.09  thf('113', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.86/5.09      inference('demod', [status(thm)], ['111', '112'])).
% 4.86/5.09  thf('114', plain, (((v2_funct_1 @ sk_C))),
% 4.86/5.09      inference('demod', [status(thm)], ['90', '113'])).
% 4.86/5.09  thf('115', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 4.86/5.09      inference('split', [status(esa)], ['0'])).
% 4.86/5.09  thf('116', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.86/5.09      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 4.86/5.09  thf('117', plain, ($false),
% 4.86/5.09      inference('simpl_trail', [status(thm)], ['77', '116'])).
% 4.86/5.09  
% 4.86/5.09  % SZS output end Refutation
% 4.86/5.09  
% 4.86/5.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
