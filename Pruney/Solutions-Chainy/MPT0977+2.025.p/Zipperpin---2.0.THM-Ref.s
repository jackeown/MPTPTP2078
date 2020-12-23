%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EDPXsLckGI

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:47 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 133 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  792 (1724 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('6',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k4_relset_1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_relat_1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( r2_relset_1 @ X39 @ X40 @ X38 @ X41 )
      | ( X38 != X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('28',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_relset_1 @ X39 @ X40 @ X41 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('31',plain,(
    r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['14','25','29','30'])).

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
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k4_relset_1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
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

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X26 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('42',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['44','47'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ X17 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['26','28'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['34','39','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EDPXsLckGI
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 691 iterations in 0.624s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.08  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.08  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.90/1.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.08  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.90/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.08  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.08  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.90/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(t23_funct_2, conjecture,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08       ( ( r2_relset_1 @
% 0.90/1.08           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 0.90/1.08           C ) & 
% 0.90/1.08         ( r2_relset_1 @
% 0.90/1.08           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 0.90/1.08           C ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.08        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08          ( ( r2_relset_1 @
% 0.90/1.08              A @ B @ 
% 0.90/1.08              ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C ) & 
% 0.90/1.08            ( r2_relset_1 @
% 0.90/1.08              A @ B @ 
% 0.90/1.08              ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t23_funct_2])).
% 0.90/1.08  thf('0', plain,
% 0.90/1.08      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.90/1.08            sk_C) @ 
% 0.90/1.08           sk_C)
% 0.90/1.08        | ~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.90/1.08              (k6_partfun1 @ sk_B)) @ 
% 0.90/1.08             sk_C))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.90/1.08            (k6_partfun1 @ sk_B)) @ 
% 0.90/1.08           sk_C))
% 0.90/1.08         <= (~
% 0.90/1.08             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.90/1.08                (k6_partfun1 @ sk_B)) @ 
% 0.90/1.08               sk_C)))),
% 0.90/1.08      inference('split', [status(esa)], ['0'])).
% 0.90/1.08  thf(redefinition_k6_partfun1, axiom,
% 0.90/1.08    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.90/1.08  thf('2', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.90/1.08            (k6_relat_1 @ sk_B)) @ 
% 0.90/1.08           sk_C))
% 0.90/1.08         <= (~
% 0.90/1.08             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.90/1.08                (k6_partfun1 @ sk_B)) @ 
% 0.90/1.08               sk_C)))),
% 0.90/1.08      inference('demod', [status(thm)], ['1', '2'])).
% 0.90/1.08  thf(t94_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      (![X18 : $i, X19 : $i]:
% 0.90/1.08         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.90/1.08          | ~ (v1_relat_1 @ X19))),
% 0.90/1.08      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(t29_relset_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( m1_subset_1 @
% 0.90/1.08       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (![X42 : $i]:
% 0.90/1.08         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 0.90/1.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.90/1.08  thf(redefinition_k4_relset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.08     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.08         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.08       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.90/1.08          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.90/1.08          | ((k4_relset_1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.90/1.08              = (k5_relat_1 @ X32 @ X35)))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.08         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 0.90/1.08            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.90/1.08          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_relat_1 @ X0) @ sk_C)
% 0.90/1.08           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))),
% 0.90/1.08      inference('sup-', [status(thm)], ['5', '8'])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.90/1.08            sk_C) @ 
% 0.90/1.08           sk_C))
% 0.90/1.08         <= (~
% 0.90/1.08             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.08                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.90/1.08               sk_C)))),
% 0.90/1.08      inference('split', [status(esa)], ['0'])).
% 0.90/1.08  thf('11', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ 
% 0.90/1.08            sk_C) @ 
% 0.90/1.08           sk_C))
% 0.90/1.08         <= (~
% 0.90/1.08             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.08                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.90/1.08               sk_C)))),
% 0.90/1.08      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08           (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ sk_C))
% 0.90/1.08         <= (~
% 0.90/1.08             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.08                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.90/1.08               sk_C)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['9', '12'])).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (((~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_C @ sk_A) @ sk_C)
% 0.90/1.08         | ~ (v1_relat_1 @ sk_C)))
% 0.90/1.08         <= (~
% 0.90/1.08             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.90/1.08                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.90/1.08               sk_C)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['4', '13'])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(cc2_relset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.08         ((v4_relat_1 @ X23 @ X24)
% 0.90/1.08          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.90/1.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.90/1.08  thf('17', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.90/1.08      inference('sup-', [status(thm)], ['15', '16'])).
% 0.90/1.08  thf(t209_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.90/1.08       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i]:
% 0.90/1.08         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.90/1.08          | ~ (v4_relat_1 @ X9 @ X10)
% 0.90/1.08          | ~ (v1_relat_1 @ X9))),
% 0.90/1.08      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(cc2_relat_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ A ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.90/1.08  thf('21', plain,
% 0.90/1.08      (![X3 : $i, X4 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.90/1.08          | (v1_relat_1 @ X3)
% 0.90/1.08          | ~ (v1_relat_1 @ X4))),
% 0.90/1.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.90/1.08      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.08  thf(fc6_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.08  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.08      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.08  thf('25', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.90/1.08      inference('demod', [status(thm)], ['19', '24'])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(redefinition_r2_relset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.08       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.90/1.08  thf('27', plain,
% 0.90/1.08      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.90/1.08          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.90/1.08          | (r2_relset_1 @ X39 @ X40 @ X38 @ X41)
% 0.90/1.08          | ((X38) != (X41)))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.90/1.08         ((r2_relset_1 @ X39 @ X40 @ X41 @ X41)
% 0.90/1.08          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.90/1.08      inference('simplify', [status(thm)], ['27'])).
% 0.90/1.08  thf('29', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.90/1.08      inference('sup-', [status(thm)], ['26', '28'])).
% 0.90/1.08  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.08      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.90/1.08         sk_C))),
% 0.90/1.08      inference('demod', [status(thm)], ['14', '25', '29', '30'])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      (~
% 0.90/1.08       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.90/1.08         sk_C)) | 
% 0.90/1.08       ~
% 0.90/1.08       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.90/1.08         sk_C))),
% 0.90/1.08      inference('split', [status(esa)], ['0'])).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      (~
% 0.90/1.08       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.90/1.08         sk_C))),
% 0.90/1.08      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.90/1.08  thf('34', plain,
% 0.90/1.08      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.90/1.08          (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_relat_1 @ sk_B)) @ 
% 0.90/1.08          sk_C)),
% 0.90/1.08      inference('simpl_trail', [status(thm)], ['3', '33'])).
% 0.90/1.08  thf('35', plain,
% 0.90/1.08      (![X42 : $i]:
% 0.90/1.08         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 0.90/1.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('37', plain,
% 0.90/1.08      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.90/1.08          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.90/1.08          | ((k4_relset_1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.90/1.08              = (k5_relat_1 @ X32 @ X35)))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.90/1.08  thf('38', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.08            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['36', '37'])).
% 0.90/1.08  thf('39', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ (k6_relat_1 @ X0))
% 0.90/1.08           = (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['35', '38'])).
% 0.90/1.08  thf('40', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(dt_k2_relset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.90/1.08  thf('41', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.90/1.08         ((m1_subset_1 @ (k2_relset_1 @ X26 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 0.90/1.08          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.90/1.08      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.90/1.08  thf('42', plain,
% 0.90/1.08      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.08  thf(t3_subset, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.08  thf('43', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.08  thf('44', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.90/1.08      inference('sup-', [status(thm)], ['42', '43'])).
% 0.90/1.08  thf('45', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.08       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.08  thf('46', plain,
% 0.90/1.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.08         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.90/1.08          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.08  thf('47', plain,
% 0.90/1.08      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.90/1.08      inference('sup-', [status(thm)], ['45', '46'])).
% 0.90/1.08  thf('48', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.90/1.08      inference('demod', [status(thm)], ['44', '47'])).
% 0.90/1.08  thf(t79_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.90/1.08         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.90/1.08  thf('49', plain,
% 0.90/1.08      (![X16 : $i, X17 : $i]:
% 0.90/1.08         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.90/1.08          | ((k5_relat_1 @ X16 @ (k6_relat_1 @ X17)) = (X16))
% 0.90/1.08          | ~ (v1_relat_1 @ X16))),
% 0.90/1.08      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.90/1.08  thf('50', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ sk_C)
% 0.90/1.08        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['48', '49'])).
% 0.90/1.08  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.08      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.08  thf('52', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.90/1.08      inference('demod', [status(thm)], ['50', '51'])).
% 0.90/1.08  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.90/1.08      inference('sup-', [status(thm)], ['26', '28'])).
% 0.90/1.08  thf('54', plain, ($false),
% 0.90/1.08      inference('demod', [status(thm)], ['34', '39', '52', '53'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
