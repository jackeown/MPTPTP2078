%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HA3mTLrLyu

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 225 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  755 (3547 expanded)
%              Number of equality atoms :   14 (  90 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k1_relat_1 @ X3 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( v1_funct_2 @ X13 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('28',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','48','49'])).

thf('51',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('54',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('55',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf('56',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k1_relat_1 @ X3 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['51','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HA3mTLrLyu
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:33:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 61 iterations in 0.039s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(t31_funct_2, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.50       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.22/0.50         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.22/0.50           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.22/0.50           ( m1_subset_1 @
% 0.22/0.50             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.50            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.50          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.22/0.50            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.22/0.50              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.22/0.50              ( m1_subset_1 @
% 0.22/0.50                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.50        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.22/0.50        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.22/0.50         <= (~
% 0.22/0.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc1_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( v1_relat_1 @ C ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.50         ((v1_relat_1 @ X4)
% 0.22/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.50  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(dt_k2_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.50         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X2 : $i]:
% 0.22/0.50         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.22/0.50          | ~ (v1_funct_1 @ X2)
% 0.22/0.50          | ~ (v1_relat_1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.22/0.50         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.22/0.50         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '9'])).
% 0.22/0.50  thf(t55_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ( v2_funct_1 @ A ) =>
% 0.22/0.50         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.22/0.50           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X3 : $i]:
% 0.22/0.50         (~ (v2_funct_1 @ X3)
% 0.22/0.50          | ((k2_relat_1 @ X3) = (k1_relat_1 @ (k2_funct_1 @ X3)))
% 0.22/0.50          | ~ (v1_funct_1 @ X3)
% 0.22/0.50          | ~ (v1_relat_1 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X2 : $i]:
% 0.22/0.50         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.22/0.50          | ~ (v1_funct_1 @ X2)
% 0.22/0.50          | ~ (v1_relat_1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X2 : $i]:
% 0.22/0.50         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.22/0.50          | ~ (v1_funct_1 @ X2)
% 0.22/0.50          | ~ (v1_relat_1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X7 @ X8)
% 0.22/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('16', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf(d18_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (v4_relat_1 @ X0 @ X1)
% 0.22/0.50          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v2_funct_1 @ X3)
% 0.22/0.51          | ((k1_relat_1 @ X3) = (k2_relat_1 @ (k2_funct_1 @ X3)))
% 0.22/0.51          | ~ (v1_funct_1 @ X3)
% 0.22/0.51          | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.51  thf(t4_funct_2, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.51         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.22/0.51           ( m1_subset_1 @
% 0.22/0.51             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.22/0.51          | (v1_funct_2 @ X13 @ (k1_relat_1 @ X13) @ X14)
% 0.22/0.51          | ~ (v1_funct_1 @ X13)
% 0.22/0.51          | ~ (v1_relat_1 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v2_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.51          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.22/0.51             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.22/0.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | ~ (v2_funct_1 @ sk_C)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '23'])).
% 0.22/0.51  thf('25', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.22/0.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '28'])).
% 0.22/0.51  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '32'])).
% 0.22/0.51  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.22/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | ~ (v2_funct_1 @ sk_C))),
% 0.22/0.51      inference('sup+', [status(thm)], ['11', '36'])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.22/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.22/0.51      inference('sup+', [status(thm)], ['40', '41'])).
% 0.22/0.51  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('46', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.22/0.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('48', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.22/0.51       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.22/0.51       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['10', '48', '49'])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v2_funct_1 @ X3)
% 0.22/0.51          | ((k2_relat_1 @ X3) = (k1_relat_1 @ (k2_funct_1 @ X3)))
% 0.22/0.51          | ~ (v1_funct_1 @ X3)
% 0.22/0.51          | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.51  thf('53', plain,
% 0.22/0.51      (![X2 : $i]:
% 0.22/0.51         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.22/0.51          | ~ (v1_funct_1 @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      (![X2 : $i]:
% 0.22/0.51         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.22/0.51          | ~ (v1_funct_1 @ X2)
% 0.22/0.51          | ~ (v1_relat_1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.51  thf('55', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      (![X3 : $i]:
% 0.22/0.51         (~ (v2_funct_1 @ X3)
% 0.22/0.51          | ((k1_relat_1 @ X3) = (k2_relat_1 @ (k2_funct_1 @ X3)))
% 0.22/0.51          | ~ (v1_funct_1 @ X3)
% 0.22/0.51          | ~ (v1_relat_1 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.51  thf('57', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.22/0.51          | (m1_subset_1 @ X13 @ 
% 0.22/0.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X13) @ X14)))
% 0.22/0.51          | ~ (v1_funct_1 @ X13)
% 0.22/0.51          | ~ (v1_relat_1 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v2_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.22/0.51          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.22/0.51             (k1_zfmisc_1 @ 
% 0.22/0.51              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.51  thf('59', plain,
% 0.22/0.51      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51         (k1_zfmisc_1 @ 
% 0.22/0.51          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.22/0.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | ~ (v2_funct_1 @ sk_C)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['55', '58'])).
% 0.22/0.51  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51         (k1_zfmisc_1 @ 
% 0.22/0.51          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.22/0.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51           (k1_zfmisc_1 @ 
% 0.22/0.51            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['54', '63'])).
% 0.22/0.51  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.22/0.51        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51           (k1_zfmisc_1 @ 
% 0.22/0.51            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51           (k1_zfmisc_1 @ 
% 0.22/0.51            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['53', '67'])).
% 0.22/0.51  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.22/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51        | ~ (v2_funct_1 @ sk_C))),
% 0.22/0.51      inference('sup+', [status(thm)], ['52', '71'])).
% 0.22/0.51  thf('73', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.22/0.51      inference('sup+', [status(thm)], ['40', '41'])).
% 0.22/0.51  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('76', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('77', plain,
% 0.22/0.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.22/0.51  thf('78', plain, ($false), inference('demod', [status(thm)], ['51', '77'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
