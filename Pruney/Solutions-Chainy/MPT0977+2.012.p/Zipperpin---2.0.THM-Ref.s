%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hUyoiUdHbH

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 130 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  734 (1692 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t23_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
          & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_funct_2])).

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('7',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17 )
        = ( k5_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_relat_1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2
        = ( k7_relat_1 @ X2 @ X3 ) )
      | ~ ( v4_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['27'])).

thf('29',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('31',plain,(
    r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['16','25','29','30'])).

thf('32',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['3','33'])).

thf('35',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17 )
        = ( k5_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('46',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ X5 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('50',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['26','28'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['34','39','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hUyoiUdHbH
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:50:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 43 iterations in 0.022s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.19/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.46  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.46  thf(t23_funct_2, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( r2_relset_1 @
% 0.19/0.46           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 0.19/0.46           C ) & 
% 0.19/0.46         ( r2_relset_1 @
% 0.19/0.46           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 0.19/0.46           C ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46          ( ( r2_relset_1 @
% 0.19/0.46              A @ B @ 
% 0.19/0.46              ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C ) & 
% 0.19/0.46            ( r2_relset_1 @
% 0.19/0.46              A @ B @ 
% 0.19/0.46              ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t23_funct_2])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.19/0.46            sk_C) @ 
% 0.19/0.46           sk_C)
% 0.19/0.46        | ~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.46              (k6_partfun1 @ sk_B)) @ 
% 0.19/0.46             sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.46            (k6_partfun1 @ sk_B)) @ 
% 0.19/0.46           sk_C))
% 0.19/0.46         <= (~
% 0.19/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.46                (k6_partfun1 @ sk_B)) @ 
% 0.19/0.46               sk_C)))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf(redefinition_k6_partfun1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.46  thf('2', plain, (![X26 : $i]: ((k6_partfun1 @ X26) = (k6_relat_1 @ X26))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.46            (k6_relat_1 @ sk_B)) @ 
% 0.19/0.46           sk_C))
% 0.19/0.46         <= (~
% 0.19/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.19/0.46                (k6_partfun1 @ sk_B)) @ 
% 0.19/0.46               sk_C)))),
% 0.19/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t94_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i]:
% 0.19/0.46         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 0.19/0.46          | ~ (v1_relat_1 @ X7))),
% 0.19/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_k6_partfun1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( m1_subset_1 @
% 0.19/0.46         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.19/0.46       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X25 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.19/0.46  thf('7', plain, (![X26 : $i]: ((k6_partfun1 @ X26) = (k6_relat_1 @ X26))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X25 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.19/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf(redefinition_k4_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.46     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.46         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.46       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.19/0.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.19/0.46          | ((k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17)
% 0.19/0.46              = (k5_relat_1 @ X14 @ X17)))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 0.19/0.46            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_relat_1 @ X0) @ sk_C)
% 0.19/0.46           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.19/0.46            sk_C) @ 
% 0.19/0.46           sk_C))
% 0.19/0.46         <= (~
% 0.19/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.46               sk_C)))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf('13', plain, (![X26 : $i]: ((k6_partfun1 @ X26) = (k6_relat_1 @ X26))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ 
% 0.19/0.46            sk_C) @ 
% 0.19/0.46           sk_C))
% 0.19/0.46         <= (~
% 0.19/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.46               sk_C)))),
% 0.19/0.46      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ sk_C))
% 0.19/0.46         <= (~
% 0.19/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.46               sk_C)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['11', '14'])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (((~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_C @ sk_A) @ sk_C)
% 0.19/0.46         | ~ (v1_relat_1 @ sk_C)))
% 0.19/0.46         <= (~
% 0.19/0.46             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.19/0.46                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.46               sk_C)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '15'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc2_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         ((v4_relat_1 @ X11 @ X12)
% 0.19/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.46  thf('19', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.46  thf(t209_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (((X2) = (k7_relat_1 @ X2 @ X3))
% 0.19/0.46          | ~ (v4_relat_1 @ X2 @ X3)
% 0.19/0.46          | ~ (v1_relat_1 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc1_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( v1_relat_1 @ C ) ))).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.46         ((v1_relat_1 @ X8)
% 0.19/0.46          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.46  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.46  thf('25', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['21', '24'])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(reflexivity_r2_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.46       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.46         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 0.19/0.46          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.19/0.46          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.19/0.46      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.19/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.46      inference('condensation', [status(thm)], ['27'])).
% 0.19/0.46  thf('29', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['26', '28'])).
% 0.19/0.46  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      (((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.46         sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['16', '25', '29', '30'])).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      (~
% 0.19/0.46       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.19/0.46         sk_C)) | 
% 0.19/0.46       ~
% 0.19/0.46       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.19/0.46         sk_C))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      (~
% 0.19/0.46       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.19/0.46         sk_C))),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.19/0.46  thf('34', plain,
% 0.19/0.46      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.19/0.46          (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_relat_1 @ sk_B)) @ 
% 0.19/0.46          sk_C)),
% 0.19/0.46      inference('simpl_trail', [status(thm)], ['3', '33'])).
% 0.19/0.46  thf('35', plain,
% 0.19/0.46      (![X25 : $i]:
% 0.19/0.46         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 0.19/0.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.19/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf('36', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('37', plain,
% 0.19/0.46      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.19/0.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.19/0.46          | ((k4_relset_1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17)
% 0.19/0.46              = (k5_relat_1 @ X14 @ X17)))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.19/0.46  thf('38', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.19/0.46            = (k5_relat_1 @ sk_C @ X0))
% 0.19/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.46  thf('39', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ (k6_relat_1 @ X0))
% 0.19/0.46           = (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['35', '38'])).
% 0.19/0.46  thf('40', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('41', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         ((v5_relat_1 @ X11 @ X13)
% 0.19/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.46  thf('42', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.46  thf(d19_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.46  thf('43', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v5_relat_1 @ X0 @ X1)
% 0.19/0.46          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.46  thf('44', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.46  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.46  thf('46', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.19/0.46      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.46  thf(t79_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.19/0.46         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.19/0.46  thf('47', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.19/0.46          | ((k5_relat_1 @ X4 @ (k6_relat_1 @ X5)) = (X4))
% 0.19/0.46          | ~ (v1_relat_1 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.19/0.46  thf('48', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.46        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.46  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.46  thf('50', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['48', '49'])).
% 0.19/0.46  thf('51', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['26', '28'])).
% 0.19/0.46  thf('52', plain, ($false),
% 0.19/0.46      inference('demod', [status(thm)], ['34', '39', '50', '51'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
