%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1jeOZZwGZy

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:25 EST 2020

% Result     : Theorem 4.75s
% Output     : Refutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  206 (1336 expanded)
%              Number of leaves         :   46 ( 398 expanded)
%              Depth                    :   26
%              Number of atoms          : 1495 (25606 expanded)
%              Number of equality atoms :   71 ( 334 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','23'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( v5_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','33','38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('52',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('55',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('56',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('59',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('63',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('68',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('70',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['45','58','61','68','69','70'])).

thf('72',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( v5_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
       != X29 )
      | ( v2_funct_2 @ X30 @ X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('77',plain,(
    ! [X30: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
      | ( v2_funct_2 @ X30 @ ( k2_relat_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['71','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('82',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('94',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('98',plain,(
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

thf('99',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44 ) )
      | ( v2_funct_1 @ X48 )
      | ( X46 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('110',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('111',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('112',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('114',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('115',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['113','114'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('117',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('118',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('119',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('122',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('123',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('124',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('126',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('129',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['118','129'])).

thf('131',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['116','133'])).

thf('135',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['122','123'])).

thf('138',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('139',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('140',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['122','123'])).

thf('143',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('144',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('145',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['136','141','146'])).

thf('148',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['113','114'])).

thf('149',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','115','147','148'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('150',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('151',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('153',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['122','123'])).

thf('156',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('157',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    $false ),
    inference(demod,[status(thm)],['87','154','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1jeOZZwGZy
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.75/4.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.75/4.94  % Solved by: fo/fo7.sh
% 4.75/4.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.75/4.94  % done 4380 iterations in 4.482s
% 4.75/4.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.75/4.94  % SZS output start Refutation
% 4.75/4.94  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.75/4.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.75/4.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.75/4.94  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.75/4.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.75/4.94  thf(sk_B_type, type, sk_B: $i).
% 4.75/4.94  thf(sk_A_type, type, sk_A: $i).
% 4.75/4.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.75/4.94  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.75/4.94  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.75/4.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.75/4.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.75/4.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.75/4.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.75/4.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.75/4.94  thf(sk_D_type, type, sk_D: $i).
% 4.75/4.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.75/4.94  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.75/4.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.75/4.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.75/4.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.75/4.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.75/4.94  thf(sk_C_type, type, sk_C: $i).
% 4.75/4.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.75/4.94  thf(t29_funct_2, conjecture,
% 4.75/4.94    (![A:$i,B:$i,C:$i]:
% 4.75/4.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.75/4.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.75/4.94       ( ![D:$i]:
% 4.75/4.94         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.75/4.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.75/4.94           ( ( r2_relset_1 @
% 4.75/4.94               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.75/4.94               ( k6_partfun1 @ A ) ) =>
% 4.75/4.94             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.75/4.94  thf(zf_stmt_0, negated_conjecture,
% 4.75/4.94    (~( ![A:$i,B:$i,C:$i]:
% 4.75/4.94        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.75/4.94            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.75/4.94          ( ![D:$i]:
% 4.75/4.94            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.75/4.94                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.75/4.94              ( ( r2_relset_1 @
% 4.75/4.94                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.75/4.94                  ( k6_partfun1 @ A ) ) =>
% 4.75/4.94                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.75/4.94    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.75/4.94  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.75/4.94      inference('split', [status(esa)], ['0'])).
% 4.75/4.94  thf('2', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('3', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf(dt_k1_partfun1, axiom,
% 4.75/4.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.75/4.94     ( ( ( v1_funct_1 @ E ) & 
% 4.75/4.94         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.75/4.94         ( v1_funct_1 @ F ) & 
% 4.75/4.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.75/4.94       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.75/4.94         ( m1_subset_1 @
% 4.75/4.94           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.75/4.94           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.75/4.94  thf('4', plain,
% 4.75/4.94      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.75/4.94         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 4.75/4.94          | ~ (v1_funct_1 @ X31)
% 4.75/4.94          | ~ (v1_funct_1 @ X34)
% 4.75/4.94          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.75/4.94          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 4.75/4.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 4.75/4.94      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.75/4.94  thf('5', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.94         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.75/4.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.75/4.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.75/4.94          | ~ (v1_funct_1 @ X1)
% 4.75/4.94          | ~ (v1_funct_1 @ sk_C))),
% 4.75/4.94      inference('sup-', [status(thm)], ['3', '4'])).
% 4.75/4.94  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('7', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.94         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.75/4.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.75/4.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.75/4.94          | ~ (v1_funct_1 @ X1))),
% 4.75/4.94      inference('demod', [status(thm)], ['5', '6'])).
% 4.75/4.94  thf('8', plain,
% 4.75/4.94      ((~ (v1_funct_1 @ sk_D)
% 4.75/4.94        | (m1_subset_1 @ 
% 4.75/4.94           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.75/4.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.75/4.94      inference('sup-', [status(thm)], ['2', '7'])).
% 4.75/4.94  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('10', plain,
% 4.75/4.94      ((m1_subset_1 @ 
% 4.75/4.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.75/4.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.75/4.94      inference('demod', [status(thm)], ['8', '9'])).
% 4.75/4.94  thf(cc2_relat_1, axiom,
% 4.75/4.94    (![A:$i]:
% 4.75/4.94     ( ( v1_relat_1 @ A ) =>
% 4.75/4.94       ( ![B:$i]:
% 4.75/4.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.75/4.94  thf('11', plain,
% 4.75/4.94      (![X6 : $i, X7 : $i]:
% 4.75/4.94         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 4.75/4.94          | (v1_relat_1 @ X6)
% 4.75/4.94          | ~ (v1_relat_1 @ X7))),
% 4.75/4.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.75/4.94  thf('12', plain,
% 4.75/4.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 4.75/4.94        | (v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['10', '11'])).
% 4.75/4.94  thf(fc6_relat_1, axiom,
% 4.75/4.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.75/4.94  thf('13', plain,
% 4.75/4.94      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 4.75/4.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.75/4.94  thf('14', plain,
% 4.75/4.94      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['12', '13'])).
% 4.75/4.94  thf('15', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('16', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf(redefinition_k1_partfun1, axiom,
% 4.75/4.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.75/4.94     ( ( ( v1_funct_1 @ E ) & 
% 4.75/4.94         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.75/4.94         ( v1_funct_1 @ F ) & 
% 4.75/4.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.75/4.94       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.75/4.94  thf('17', plain,
% 4.75/4.94      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 4.75/4.94         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 4.75/4.94          | ~ (v1_funct_1 @ X37)
% 4.75/4.94          | ~ (v1_funct_1 @ X40)
% 4.75/4.94          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 4.75/4.94          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 4.75/4.94              = (k5_relat_1 @ X37 @ X40)))),
% 4.75/4.94      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.75/4.94  thf('18', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.75/4.94            = (k5_relat_1 @ sk_C @ X0))
% 4.75/4.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.75/4.94          | ~ (v1_funct_1 @ X0)
% 4.75/4.94          | ~ (v1_funct_1 @ sk_C))),
% 4.75/4.94      inference('sup-', [status(thm)], ['16', '17'])).
% 4.75/4.94  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('20', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.75/4.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.75/4.94            = (k5_relat_1 @ sk_C @ X0))
% 4.75/4.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.75/4.94          | ~ (v1_funct_1 @ X0))),
% 4.75/4.94      inference('demod', [status(thm)], ['18', '19'])).
% 4.75/4.94  thf('21', plain,
% 4.75/4.94      ((~ (v1_funct_1 @ sk_D)
% 4.75/4.94        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.75/4.94            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['15', '20'])).
% 4.75/4.94  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('23', plain,
% 4.75/4.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.75/4.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['21', '22'])).
% 4.75/4.94  thf('24', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['14', '23'])).
% 4.75/4.94  thf(t45_relat_1, axiom,
% 4.75/4.94    (![A:$i]:
% 4.75/4.94     ( ( v1_relat_1 @ A ) =>
% 4.75/4.94       ( ![B:$i]:
% 4.75/4.94         ( ( v1_relat_1 @ B ) =>
% 4.75/4.94           ( r1_tarski @
% 4.75/4.94             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 4.75/4.94  thf('25', plain,
% 4.75/4.94      (![X14 : $i, X15 : $i]:
% 4.75/4.94         (~ (v1_relat_1 @ X14)
% 4.75/4.94          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 4.75/4.94             (k2_relat_1 @ X14))
% 4.75/4.94          | ~ (v1_relat_1 @ X15))),
% 4.75/4.94      inference('cnf', [status(esa)], [t45_relat_1])).
% 4.75/4.94  thf(d19_relat_1, axiom,
% 4.75/4.94    (![A:$i,B:$i]:
% 4.75/4.94     ( ( v1_relat_1 @ B ) =>
% 4.75/4.94       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.75/4.94  thf('26', plain,
% 4.75/4.94      (![X10 : $i, X11 : $i]:
% 4.75/4.94         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 4.75/4.94          | (v5_relat_1 @ X10 @ X11)
% 4.75/4.94          | ~ (v1_relat_1 @ X10))),
% 4.75/4.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.75/4.94  thf('27', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i]:
% 4.75/4.94         (~ (v1_relat_1 @ X1)
% 4.75/4.94          | ~ (v1_relat_1 @ X0)
% 4.75/4.94          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 4.75/4.94          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['25', '26'])).
% 4.75/4.94  thf('28', plain,
% 4.75/4.94      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 4.75/4.94        | ~ (v1_relat_1 @ sk_D)
% 4.75/4.94        | ~ (v1_relat_1 @ sk_C))),
% 4.75/4.94      inference('sup-', [status(thm)], ['24', '27'])).
% 4.75/4.94  thf('29', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('30', plain,
% 4.75/4.94      (![X6 : $i, X7 : $i]:
% 4.75/4.94         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 4.75/4.94          | (v1_relat_1 @ X6)
% 4.75/4.94          | ~ (v1_relat_1 @ X7))),
% 4.75/4.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.75/4.94  thf('31', plain,
% 4.75/4.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.75/4.94      inference('sup-', [status(thm)], ['29', '30'])).
% 4.75/4.94  thf('32', plain,
% 4.75/4.94      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 4.75/4.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.75/4.94  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 4.75/4.94      inference('demod', [status(thm)], ['31', '32'])).
% 4.75/4.94  thf('34', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('35', plain,
% 4.75/4.94      (![X6 : $i, X7 : $i]:
% 4.75/4.94         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 4.75/4.94          | (v1_relat_1 @ X6)
% 4.75/4.94          | ~ (v1_relat_1 @ X7))),
% 4.75/4.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.75/4.94  thf('36', plain,
% 4.75/4.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.75/4.94      inference('sup-', [status(thm)], ['34', '35'])).
% 4.75/4.94  thf('37', plain,
% 4.75/4.94      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 4.75/4.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.75/4.94  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.94      inference('demod', [status(thm)], ['36', '37'])).
% 4.75/4.94  thf('39', plain,
% 4.75/4.94      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['28', '33', '38'])).
% 4.75/4.94  thf('40', plain,
% 4.75/4.94      (![X10 : $i, X11 : $i]:
% 4.75/4.94         (~ (v5_relat_1 @ X10 @ X11)
% 4.75/4.94          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 4.75/4.94          | ~ (v1_relat_1 @ X10))),
% 4.75/4.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.75/4.94  thf('41', plain,
% 4.75/4.94      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.75/4.94        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 4.75/4.94           (k2_relat_1 @ sk_D)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['39', '40'])).
% 4.75/4.94  thf('42', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['14', '23'])).
% 4.75/4.94  thf('43', plain,
% 4.75/4.94      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 4.75/4.94        (k2_relat_1 @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['41', '42'])).
% 4.75/4.94  thf(d10_xboole_0, axiom,
% 4.75/4.94    (![A:$i,B:$i]:
% 4.75/4.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.75/4.94  thf('44', plain,
% 4.75/4.94      (![X1 : $i, X3 : $i]:
% 4.75/4.94         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 4.75/4.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.75/4.94  thf('45', plain,
% 4.75/4.94      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 4.75/4.94           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 4.75/4.94        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 4.75/4.94      inference('sup-', [status(thm)], ['43', '44'])).
% 4.75/4.94  thf('46', plain,
% 4.75/4.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.75/4.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.75/4.94        (k6_partfun1 @ sk_A))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('47', plain,
% 4.75/4.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.75/4.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['21', '22'])).
% 4.75/4.94  thf('48', plain,
% 4.75/4.94      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.75/4.94        (k6_partfun1 @ sk_A))),
% 4.75/4.94      inference('demod', [status(thm)], ['46', '47'])).
% 4.75/4.94  thf('49', plain,
% 4.75/4.94      ((m1_subset_1 @ 
% 4.75/4.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.75/4.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.75/4.94      inference('demod', [status(thm)], ['8', '9'])).
% 4.75/4.94  thf('50', plain,
% 4.75/4.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.75/4.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['21', '22'])).
% 4.75/4.94  thf('51', plain,
% 4.75/4.94      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.75/4.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.75/4.94      inference('demod', [status(thm)], ['49', '50'])).
% 4.75/4.94  thf(redefinition_r2_relset_1, axiom,
% 4.75/4.94    (![A:$i,B:$i,C:$i,D:$i]:
% 4.75/4.94     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.75/4.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.75/4.94       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.75/4.94  thf('52', plain,
% 4.75/4.94      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 4.75/4.94         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.75/4.94          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.75/4.94          | ((X24) = (X27))
% 4.75/4.94          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 4.75/4.94      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.75/4.94  thf('53', plain,
% 4.75/4.94      (![X0 : $i]:
% 4.75/4.94         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 4.75/4.94          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 4.75/4.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.75/4.94      inference('sup-', [status(thm)], ['51', '52'])).
% 4.75/4.94  thf('54', plain,
% 4.75/4.94      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.75/4.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.75/4.94        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['48', '53'])).
% 4.75/4.94  thf(t29_relset_1, axiom,
% 4.75/4.94    (![A:$i]:
% 4.75/4.94     ( m1_subset_1 @
% 4.75/4.94       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.75/4.94  thf('55', plain,
% 4.75/4.94      (![X28 : $i]:
% 4.75/4.94         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 4.75/4.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 4.75/4.94      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.75/4.94  thf(redefinition_k6_partfun1, axiom,
% 4.75/4.94    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.75/4.94  thf('56', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 4.75/4.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.75/4.94  thf('57', plain,
% 4.75/4.94      (![X28 : $i]:
% 4.75/4.94         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 4.75/4.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 4.75/4.94      inference('demod', [status(thm)], ['55', '56'])).
% 4.75/4.94  thf('58', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.75/4.94      inference('demod', [status(thm)], ['54', '57'])).
% 4.75/4.94  thf(t71_relat_1, axiom,
% 4.75/4.94    (![A:$i]:
% 4.75/4.94     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.75/4.94       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.75/4.94  thf('59', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 4.75/4.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.75/4.94  thf('60', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 4.75/4.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.75/4.94  thf('61', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 4.75/4.94      inference('demod', [status(thm)], ['59', '60'])).
% 4.75/4.94  thf('62', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf(cc2_relset_1, axiom,
% 4.75/4.94    (![A:$i,B:$i,C:$i]:
% 4.75/4.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.75/4.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.75/4.94  thf('63', plain,
% 4.75/4.94      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.75/4.94         ((v5_relat_1 @ X21 @ X23)
% 4.75/4.94          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.75/4.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.75/4.94  thf('64', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.75/4.94      inference('sup-', [status(thm)], ['62', '63'])).
% 4.75/4.94  thf('65', plain,
% 4.75/4.94      (![X10 : $i, X11 : $i]:
% 4.75/4.94         (~ (v5_relat_1 @ X10 @ X11)
% 4.75/4.94          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 4.75/4.94          | ~ (v1_relat_1 @ X10))),
% 4.75/4.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.75/4.94  thf('66', plain,
% 4.75/4.94      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 4.75/4.94      inference('sup-', [status(thm)], ['64', '65'])).
% 4.75/4.94  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 4.75/4.94      inference('demod', [status(thm)], ['31', '32'])).
% 4.75/4.94  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 4.75/4.94      inference('demod', [status(thm)], ['66', '67'])).
% 4.75/4.94  thf('69', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.75/4.94      inference('demod', [status(thm)], ['54', '57'])).
% 4.75/4.94  thf('70', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 4.75/4.94      inference('demod', [status(thm)], ['59', '60'])).
% 4.75/4.94  thf('71', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.75/4.94      inference('demod', [status(thm)], ['45', '58', '61', '68', '69', '70'])).
% 4.75/4.94  thf('72', plain,
% 4.75/4.94      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 4.75/4.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.75/4.94  thf('73', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 4.75/4.94      inference('simplify', [status(thm)], ['72'])).
% 4.75/4.94  thf('74', plain,
% 4.75/4.94      (![X10 : $i, X11 : $i]:
% 4.75/4.94         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 4.75/4.94          | (v5_relat_1 @ X10 @ X11)
% 4.75/4.94          | ~ (v1_relat_1 @ X10))),
% 4.75/4.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.75/4.94  thf('75', plain,
% 4.75/4.94      (![X0 : $i]:
% 4.75/4.94         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['73', '74'])).
% 4.75/4.94  thf(d3_funct_2, axiom,
% 4.75/4.94    (![A:$i,B:$i]:
% 4.75/4.94     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.75/4.94       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.75/4.94  thf('76', plain,
% 4.75/4.94      (![X29 : $i, X30 : $i]:
% 4.75/4.94         (((k2_relat_1 @ X30) != (X29))
% 4.75/4.94          | (v2_funct_2 @ X30 @ X29)
% 4.75/4.94          | ~ (v5_relat_1 @ X30 @ X29)
% 4.75/4.94          | ~ (v1_relat_1 @ X30))),
% 4.75/4.94      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.75/4.94  thf('77', plain,
% 4.75/4.94      (![X30 : $i]:
% 4.75/4.94         (~ (v1_relat_1 @ X30)
% 4.75/4.94          | ~ (v5_relat_1 @ X30 @ (k2_relat_1 @ X30))
% 4.75/4.94          | (v2_funct_2 @ X30 @ (k2_relat_1 @ X30)))),
% 4.75/4.94      inference('simplify', [status(thm)], ['76'])).
% 4.75/4.94  thf('78', plain,
% 4.75/4.94      (![X0 : $i]:
% 4.75/4.94         (~ (v1_relat_1 @ X0)
% 4.75/4.94          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.75/4.94          | ~ (v1_relat_1 @ X0))),
% 4.75/4.94      inference('sup-', [status(thm)], ['75', '77'])).
% 4.75/4.94  thf('79', plain,
% 4.75/4.94      (![X0 : $i]:
% 4.75/4.94         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.75/4.94      inference('simplify', [status(thm)], ['78'])).
% 4.75/4.94  thf('80', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.75/4.94      inference('sup+', [status(thm)], ['71', '79'])).
% 4.75/4.94  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 4.75/4.94      inference('demod', [status(thm)], ['31', '32'])).
% 4.75/4.94  thf('82', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.75/4.94      inference('demod', [status(thm)], ['80', '81'])).
% 4.75/4.94  thf('83', plain,
% 4.75/4.94      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.75/4.94      inference('split', [status(esa)], ['0'])).
% 4.75/4.94  thf('84', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 4.75/4.94      inference('sup-', [status(thm)], ['82', '83'])).
% 4.75/4.94  thf('85', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.75/4.94      inference('split', [status(esa)], ['0'])).
% 4.75/4.94  thf('86', plain, (~ ((v2_funct_1 @ sk_C))),
% 4.75/4.94      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 4.75/4.94  thf('87', plain, (~ (v2_funct_1 @ sk_C)),
% 4.75/4.94      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 4.75/4.94  thf('88', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('89', plain,
% 4.75/4.94      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.75/4.94         ((v4_relat_1 @ X21 @ X22)
% 4.75/4.94          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.75/4.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.75/4.94  thf('90', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 4.75/4.94      inference('sup-', [status(thm)], ['88', '89'])).
% 4.75/4.94  thf(d18_relat_1, axiom,
% 4.75/4.94    (![A:$i,B:$i]:
% 4.75/4.94     ( ( v1_relat_1 @ B ) =>
% 4.75/4.94       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 4.75/4.94  thf('91', plain,
% 4.75/4.94      (![X8 : $i, X9 : $i]:
% 4.75/4.94         (~ (v4_relat_1 @ X8 @ X9)
% 4.75/4.94          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 4.75/4.94          | ~ (v1_relat_1 @ X8))),
% 4.75/4.94      inference('cnf', [status(esa)], [d18_relat_1])).
% 4.75/4.94  thf('92', plain,
% 4.75/4.94      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 4.75/4.94      inference('sup-', [status(thm)], ['90', '91'])).
% 4.75/4.94  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.94      inference('demod', [status(thm)], ['36', '37'])).
% 4.75/4.94  thf('94', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 4.75/4.94      inference('demod', [status(thm)], ['92', '93'])).
% 4.75/4.94  thf('95', plain,
% 4.75/4.94      (![X1 : $i, X3 : $i]:
% 4.75/4.94         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 4.75/4.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.75/4.94  thf('96', plain,
% 4.75/4.94      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 4.75/4.94        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['94', '95'])).
% 4.75/4.94  thf('97', plain,
% 4.75/4.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.75/4.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.75/4.94      inference('demod', [status(thm)], ['21', '22'])).
% 4.75/4.94  thf('98', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf(t26_funct_2, axiom,
% 4.75/4.94    (![A:$i,B:$i,C:$i,D:$i]:
% 4.75/4.94     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.75/4.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.75/4.94       ( ![E:$i]:
% 4.75/4.94         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.75/4.94             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.75/4.94           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.75/4.94             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.75/4.94               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.75/4.94  thf('99', plain,
% 4.75/4.94      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 4.75/4.94         (~ (v1_funct_1 @ X44)
% 4.75/4.94          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 4.75/4.94          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 4.75/4.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 4.75/4.94          | (v2_funct_1 @ X48)
% 4.75/4.94          | ((X46) = (k1_xboole_0))
% 4.75/4.94          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 4.75/4.94          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 4.75/4.94          | ~ (v1_funct_1 @ X48))),
% 4.75/4.94      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.75/4.94  thf('100', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i]:
% 4.75/4.94         (~ (v1_funct_1 @ X0)
% 4.75/4.94          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.75/4.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.75/4.94          | ((sk_A) = (k1_xboole_0))
% 4.75/4.94          | (v2_funct_1 @ X0)
% 4.75/4.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.75/4.94          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.75/4.94          | ~ (v1_funct_1 @ sk_D))),
% 4.75/4.94      inference('sup-', [status(thm)], ['98', '99'])).
% 4.75/4.94  thf('101', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('103', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i]:
% 4.75/4.94         (~ (v1_funct_1 @ X0)
% 4.75/4.94          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.75/4.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.75/4.94          | ((sk_A) = (k1_xboole_0))
% 4.75/4.94          | (v2_funct_1 @ X0)
% 4.75/4.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.75/4.94      inference('demod', [status(thm)], ['100', '101', '102'])).
% 4.75/4.94  thf('104', plain,
% 4.75/4.94      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.75/4.94        | (v2_funct_1 @ sk_C)
% 4.75/4.94        | ((sk_A) = (k1_xboole_0))
% 4.75/4.94        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.75/4.94        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.75/4.94        | ~ (v1_funct_1 @ sk_C))),
% 4.75/4.94      inference('sup-', [status(thm)], ['97', '103'])).
% 4.75/4.94  thf('105', plain,
% 4.75/4.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('106', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 4.75/4.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.75/4.94  thf('108', plain,
% 4.75/4.94      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.75/4.94        | (v2_funct_1 @ sk_C)
% 4.75/4.94        | ((sk_A) = (k1_xboole_0)))),
% 4.75/4.94      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 4.75/4.94  thf('109', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.75/4.94      inference('demod', [status(thm)], ['54', '57'])).
% 4.75/4.94  thf(fc4_funct_1, axiom,
% 4.75/4.94    (![A:$i]:
% 4.75/4.94     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.75/4.94       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.75/4.94  thf('110', plain, (![X20 : $i]: (v2_funct_1 @ (k6_relat_1 @ X20))),
% 4.75/4.94      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.75/4.94  thf('111', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 4.75/4.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.75/4.94  thf('112', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 4.75/4.94      inference('demod', [status(thm)], ['110', '111'])).
% 4.75/4.94  thf('113', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.75/4.94      inference('demod', [status(thm)], ['108', '109', '112'])).
% 4.75/4.94  thf('114', plain, (~ (v2_funct_1 @ sk_C)),
% 4.75/4.94      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 4.75/4.94  thf('115', plain, (((sk_A) = (k1_xboole_0))),
% 4.75/4.94      inference('clc', [status(thm)], ['113', '114'])).
% 4.75/4.94  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.75/4.94  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.75/4.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.75/4.94  thf(fc3_zfmisc_1, axiom,
% 4.75/4.94    (![A:$i,B:$i]:
% 4.75/4.94     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.75/4.94  thf('117', plain,
% 4.75/4.94      (![X4 : $i, X5 : $i]:
% 4.75/4.94         ((v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 4.75/4.94      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 4.75/4.94  thf(l13_xboole_0, axiom,
% 4.75/4.94    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.75/4.94  thf('118', plain,
% 4.75/4.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.75/4.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.75/4.94  thf('119', plain,
% 4.75/4.94      (![X4 : $i, X5 : $i]:
% 4.75/4.94         ((v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 4.75/4.94      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 4.75/4.94  thf('120', plain,
% 4.75/4.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.75/4.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.75/4.94  thf('121', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i]:
% 4.75/4.94         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['119', '120'])).
% 4.75/4.94  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 4.75/4.94  thf('122', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.94      inference('cnf', [status(esa)], [t81_relat_1])).
% 4.75/4.94  thf('123', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 4.75/4.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.75/4.94  thf('124', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.94      inference('demod', [status(thm)], ['122', '123'])).
% 4.75/4.94  thf('125', plain,
% 4.75/4.94      (![X28 : $i]:
% 4.75/4.94         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 4.75/4.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 4.75/4.94      inference('demod', [status(thm)], ['55', '56'])).
% 4.75/4.94  thf('126', plain,
% 4.75/4.94      ((m1_subset_1 @ k1_xboole_0 @ 
% 4.75/4.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 4.75/4.94      inference('sup+', [status(thm)], ['124', '125'])).
% 4.75/4.94  thf('127', plain,
% 4.75/4.94      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.75/4.94        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.75/4.94      inference('sup+', [status(thm)], ['121', '126'])).
% 4.75/4.94  thf('128', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.75/4.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.75/4.94  thf('129', plain,
% 4.75/4.94      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.75/4.94      inference('demod', [status(thm)], ['127', '128'])).
% 4.75/4.94  thf('130', plain,
% 4.75/4.94      (![X0 : $i]:
% 4.75/4.94         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 4.75/4.94          | ~ (v1_xboole_0 @ X0))),
% 4.75/4.94      inference('sup+', [status(thm)], ['118', '129'])).
% 4.75/4.94  thf('131', plain,
% 4.75/4.94      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.75/4.94         ((v4_relat_1 @ X21 @ X22)
% 4.75/4.94          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.75/4.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.75/4.94  thf('132', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i]:
% 4.75/4.94         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 4.75/4.94          | (v4_relat_1 @ k1_xboole_0 @ X1))),
% 4.75/4.94      inference('sup-', [status(thm)], ['130', '131'])).
% 4.75/4.94  thf('133', plain,
% 4.75/4.94      (![X0 : $i, X1 : $i]:
% 4.75/4.94         (~ (v1_xboole_0 @ X0) | (v4_relat_1 @ k1_xboole_0 @ X1))),
% 4.75/4.94      inference('sup-', [status(thm)], ['117', '132'])).
% 4.75/4.94  thf('134', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 4.75/4.94      inference('sup-', [status(thm)], ['116', '133'])).
% 4.75/4.94  thf('135', plain,
% 4.75/4.94      (![X8 : $i, X9 : $i]:
% 4.75/4.94         (~ (v4_relat_1 @ X8 @ X9)
% 4.75/4.94          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 4.75/4.94          | ~ (v1_relat_1 @ X8))),
% 4.75/4.94      inference('cnf', [status(esa)], [d18_relat_1])).
% 4.75/4.94  thf('136', plain,
% 4.75/4.94      (![X0 : $i]:
% 4.75/4.94         (~ (v1_relat_1 @ k1_xboole_0)
% 4.75/4.94          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 4.75/4.94      inference('sup-', [status(thm)], ['134', '135'])).
% 4.75/4.94  thf('137', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.94      inference('demod', [status(thm)], ['122', '123'])).
% 4.75/4.94  thf('138', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 4.75/4.94      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.75/4.94  thf('139', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 4.75/4.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.75/4.94  thf('140', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 4.75/4.94      inference('demod', [status(thm)], ['138', '139'])).
% 4.75/4.94  thf('141', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.75/4.94      inference('sup+', [status(thm)], ['137', '140'])).
% 4.75/4.94  thf('142', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.94      inference('demod', [status(thm)], ['122', '123'])).
% 4.75/4.94  thf('143', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 4.75/4.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.75/4.94  thf('144', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 4.75/4.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.75/4.94  thf('145', plain,
% 4.75/4.94      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 4.75/4.94      inference('demod', [status(thm)], ['143', '144'])).
% 4.75/4.94  thf('146', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.94      inference('sup+', [status(thm)], ['142', '145'])).
% 4.75/4.94  thf('147', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.75/4.94      inference('demod', [status(thm)], ['136', '141', '146'])).
% 4.75/4.94  thf('148', plain, (((sk_A) = (k1_xboole_0))),
% 4.75/4.94      inference('clc', [status(thm)], ['113', '114'])).
% 4.75/4.94  thf('149', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C))),
% 4.75/4.94      inference('demod', [status(thm)], ['96', '115', '147', '148'])).
% 4.75/4.94  thf(t64_relat_1, axiom,
% 4.75/4.94    (![A:$i]:
% 4.75/4.94     ( ( v1_relat_1 @ A ) =>
% 4.75/4.94       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 4.75/4.94           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 4.75/4.94         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 4.75/4.94  thf('150', plain,
% 4.75/4.94      (![X16 : $i]:
% 4.75/4.94         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 4.75/4.94          | ((X16) = (k1_xboole_0))
% 4.75/4.94          | ~ (v1_relat_1 @ X16))),
% 4.75/4.94      inference('cnf', [status(esa)], [t64_relat_1])).
% 4.75/4.94  thf('151', plain,
% 4.75/4.94      ((((k1_xboole_0) != (k1_xboole_0))
% 4.75/4.94        | ~ (v1_relat_1 @ sk_C)
% 4.75/4.94        | ((sk_C) = (k1_xboole_0)))),
% 4.75/4.94      inference('sup-', [status(thm)], ['149', '150'])).
% 4.75/4.94  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 4.75/4.94      inference('demod', [status(thm)], ['36', '37'])).
% 4.75/4.94  thf('153', plain,
% 4.75/4.94      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 4.75/4.94      inference('demod', [status(thm)], ['151', '152'])).
% 4.75/4.94  thf('154', plain, (((sk_C) = (k1_xboole_0))),
% 4.75/4.94      inference('simplify', [status(thm)], ['153'])).
% 4.75/4.94  thf('155', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.75/4.94      inference('demod', [status(thm)], ['122', '123'])).
% 4.75/4.94  thf('156', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 4.75/4.94      inference('demod', [status(thm)], ['110', '111'])).
% 4.75/4.94  thf('157', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.75/4.94      inference('sup+', [status(thm)], ['155', '156'])).
% 4.75/4.94  thf('158', plain, ($false),
% 4.75/4.94      inference('demod', [status(thm)], ['87', '154', '157'])).
% 4.75/4.94  
% 4.75/4.94  % SZS output end Refutation
% 4.75/4.94  
% 4.75/4.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
