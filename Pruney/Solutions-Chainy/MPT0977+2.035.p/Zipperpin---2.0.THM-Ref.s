%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWZSwcry60

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 157 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  773 (1869 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('4',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('5',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 )
        = ( k5_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['19','24'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ ( k6_relat_1 @ X11 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['14','29','33'])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['3','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 )
        = ( k5_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_relat_1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('49',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('51',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('53',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['51','52'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('57',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['30','32'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['37','42','57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWZSwcry60
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 47 iterations in 0.023s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.48  thf(t23_funct_2, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( r2_relset_1 @
% 0.20/0.48           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 0.20/0.48           C ) & 
% 0.20/0.48         ( r2_relset_1 @
% 0.20/0.48           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 0.20/0.48           C ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48          ( ( r2_relset_1 @
% 0.20/0.48              A @ B @ 
% 0.20/0.48              ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C ) & 
% 0.20/0.48            ( r2_relset_1 @
% 0.20/0.48              A @ B @ 
% 0.20/0.48              ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t23_funct_2])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.48            sk_C) @ 
% 0.20/0.48           sk_C)
% 0.20/0.48        | ~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.48              (k6_partfun1 @ sk_B)) @ 
% 0.20/0.48             sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.48            sk_C) @ 
% 0.20/0.48           sk_C))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.48                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.48               sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.48  thf('2', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ 
% 0.20/0.48            sk_C) @ 
% 0.20/0.48           sk_C))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.48                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.48               sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(dt_k6_partfun1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( m1_subset_1 @
% 0.20/0.48         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.20/0.48       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X28 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.20/0.48  thf('5', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X28 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k4_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.48     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.20/0.48       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.20/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.48          | ((k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20)
% 0.20/0.48              = (k5_relat_1 @ X17 @ X20)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.20/0.48            = (k5_relat_1 @ sk_C @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ (k6_relat_1 @ X0))
% 0.20/0.48           = (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.48            (k6_partfun1 @ sk_B)) @ 
% 0.20/0.48           sk_C))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.48                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.48               sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('12', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.48            (k6_relat_1 @ sk_B)) @ 
% 0.20/0.48           sk_C))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.48                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.48               sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48           (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_C))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.48                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.48               sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         ((v5_relat_1 @ X14 @ X16)
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.48  thf('17', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(d19_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (v5_relat_1 @ X2 @ X3)
% 0.20/0.48          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.20/0.48          | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.48          | (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf(fc6_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.48  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '24'])).
% 0.20/0.48  thf(t79_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.48         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.20/0.48          | ((k5_relat_1 @ X10 @ (k6_relat_1 @ X11)) = (X10))
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.48        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('29', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(reflexivity_r2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.48         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 0.20/0.48          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.48          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.48      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.48      inference('condensation', [status(thm)], ['31'])).
% 0.20/0.48  thf('33', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.20/0.48         sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '29', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.48         sk_C)) | 
% 0.20/0.48       ~
% 0.20/0.48       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.20/0.48         sk_C))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.48         sk_C))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.48          (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.20/0.48          sk_C)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['3', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X28 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.20/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.48          | ((k4_relset_1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20)
% 0.20/0.48              = (k5_relat_1 @ X17 @ X20)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 0.20/0.48            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_relat_1 @ X0) @ sk_C)
% 0.20/0.48           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         ((v4_relat_1 @ X14 @ X15)
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.48  thf('45', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf(t209_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.20/0.48          | ~ (v4_relat_1 @ X6 @ X7)
% 0.20/0.48          | ~ (v1_relat_1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('49', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf(t87_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X12 @ X13)) @ X13)
% 0.20/0.48          | ~ (v1_relat_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('53', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf(t77_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.48         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.20/0.48          | ((k5_relat_1 @ (k6_relat_1 @ X9) @ X8) = (X8))
% 0.20/0.48          | ~ (v1_relat_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.48        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('57', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.48  thf('59', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '42', '57', '58'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
