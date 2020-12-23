%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X516TKkZmS

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 240 expanded)
%              Number of leaves         :   25 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  790 (3952 expanded)
%              Number of equality atoms :   14 ( 100 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( v1_funct_2 @ X13 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('29',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['40','45','46','47','48'])).

thf('50',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['11','51','52'])).

thf('54',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','53'])).

thf('55',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('57',plain,(
    ! [X2: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('58',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf('59',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k1_relat_1 @ X3 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['43','44'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['54','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X516TKkZmS
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 76 iterations in 0.029s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(t31_funct_2, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.47       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.19/0.47         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.19/0.47           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.19/0.47           ( m1_subset_1 @
% 0.19/0.47             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.47            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.47          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.19/0.47            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.19/0.47              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.19/0.47              ( m1_subset_1 @
% 0.19/0.47                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.19/0.47        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.19/0.47         <= (~
% 0.19/0.47             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc1_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( v1_relat_1 @ C ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         ((v1_relat_1 @ X4)
% 0.19/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.47  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf(fc6_funct_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.19/0.47       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.19/0.47         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.19/0.47         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X2 : $i]:
% 0.19/0.47         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.19/0.47          | ~ (v2_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_relat_1 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.19/0.47         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C)))
% 0.19/0.47         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('9', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.19/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.47  thf('11', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '10'])).
% 0.19/0.47  thf(t55_funct_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.47       ( ( v2_funct_1 @ A ) =>
% 0.19/0.47         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.19/0.47           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X3 : $i]:
% 0.19/0.47         (~ (v2_funct_1 @ X3)
% 0.19/0.47          | ((k2_relat_1 @ X3) = (k1_relat_1 @ (k2_funct_1 @ X3)))
% 0.19/0.47          | ~ (v1_funct_1 @ X3)
% 0.19/0.47          | ~ (v1_relat_1 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X2 : $i]:
% 0.19/0.47         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.19/0.47          | ~ (v2_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_relat_1 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X2 : $i]:
% 0.19/0.47         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.19/0.47          | ~ (v2_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_relat_1 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc2_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.47         ((v4_relat_1 @ X7 @ X8)
% 0.19/0.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.47  thf('17', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.19/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf(d18_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ B ) =>
% 0.19/0.47       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (v4_relat_1 @ X0 @ X1)
% 0.19/0.47          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.19/0.47          | ~ (v1_relat_1 @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.47  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X3 : $i]:
% 0.19/0.47         (~ (v2_funct_1 @ X3)
% 0.19/0.47          | ((k1_relat_1 @ X3) = (k2_relat_1 @ (k2_funct_1 @ X3)))
% 0.19/0.47          | ~ (v1_funct_1 @ X3)
% 0.19/0.47          | ~ (v1_relat_1 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.19/0.47  thf(t4_funct_2, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.19/0.47         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.19/0.47           ( m1_subset_1 @
% 0.19/0.47             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.19/0.47  thf('23', plain,
% 0.19/0.47      (![X13 : $i, X14 : $i]:
% 0.19/0.47         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.19/0.47          | (v1_funct_2 @ X13 @ (k1_relat_1 @ X13) @ X14)
% 0.19/0.47          | ~ (v1_funct_1 @ X13)
% 0.19/0.47          | ~ (v1_relat_1 @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v2_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.19/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.19/0.47          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.19/0.47             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.19/0.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['21', '24'])).
% 0.19/0.47  thf('26', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('29', plain,
% 0.19/0.47      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.19/0.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.19/0.47      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['14', '29'])).
% 0.19/0.47  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.47        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '34'])).
% 0.19/0.47  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('39', plain,
% 0.19/0.47      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.19/0.47  thf('40', plain,
% 0.19/0.47      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.19/0.47        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v2_funct_1 @ sk_C))),
% 0.19/0.47      inference('sup+', [status(thm)], ['12', '39'])).
% 0.19/0.47  thf('41', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.47  thf('42', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.47         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.19/0.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.47  thf('43', plain,
% 0.19/0.47      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.47  thf('44', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('45', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.19/0.47      inference('sup+', [status(thm)], ['43', '44'])).
% 0.19/0.47  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('49', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['40', '45', '46', '47', '48'])).
% 0.19/0.47  thf('50', plain,
% 0.19/0.47      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.19/0.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('51', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.47  thf('52', plain,
% 0.19/0.47      (~
% 0.19/0.47       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.19/0.47       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.19/0.47       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('53', plain,
% 0.19/0.47      (~
% 0.19/0.47       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['11', '51', '52'])).
% 0.19/0.47  thf('54', plain,
% 0.19/0.47      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('simpl_trail', [status(thm)], ['1', '53'])).
% 0.19/0.47  thf('55', plain,
% 0.19/0.47      (![X3 : $i]:
% 0.19/0.47         (~ (v2_funct_1 @ X3)
% 0.19/0.47          | ((k2_relat_1 @ X3) = (k1_relat_1 @ (k2_funct_1 @ X3)))
% 0.19/0.47          | ~ (v1_funct_1 @ X3)
% 0.19/0.47          | ~ (v1_relat_1 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.19/0.47  thf('56', plain,
% 0.19/0.47      (![X2 : $i]:
% 0.19/0.47         ((v1_relat_1 @ (k2_funct_1 @ X2))
% 0.19/0.47          | ~ (v2_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_relat_1 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.19/0.47  thf('57', plain,
% 0.19/0.47      (![X2 : $i]:
% 0.19/0.47         ((v1_funct_1 @ (k2_funct_1 @ X2))
% 0.19/0.47          | ~ (v2_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_funct_1 @ X2)
% 0.19/0.47          | ~ (v1_relat_1 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.19/0.47  thf('58', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.47  thf('59', plain,
% 0.19/0.47      (![X3 : $i]:
% 0.19/0.47         (~ (v2_funct_1 @ X3)
% 0.19/0.47          | ((k1_relat_1 @ X3) = (k2_relat_1 @ (k2_funct_1 @ X3)))
% 0.19/0.47          | ~ (v1_funct_1 @ X3)
% 0.19/0.47          | ~ (v1_relat_1 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.19/0.47  thf('60', plain,
% 0.19/0.47      (![X13 : $i, X14 : $i]:
% 0.19/0.47         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.19/0.47          | (m1_subset_1 @ X13 @ 
% 0.19/0.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X13) @ X14)))
% 0.19/0.47          | ~ (v1_funct_1 @ X13)
% 0.19/0.47          | ~ (v1_relat_1 @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.19/0.47  thf('61', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.19/0.47          | ~ (v1_relat_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v2_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.19/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.19/0.47          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.19/0.47             (k1_zfmisc_1 @ 
% 0.19/0.47              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.47  thf('62', plain,
% 0.19/0.47      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47         (k1_zfmisc_1 @ 
% 0.19/0.47          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.19/0.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['58', '61'])).
% 0.19/0.47  thf('63', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('66', plain,
% 0.19/0.47      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47         (k1_zfmisc_1 @ 
% 0.19/0.47          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.19/0.47        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.19/0.47      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.19/0.47  thf('67', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47           (k1_zfmisc_1 @ 
% 0.19/0.47            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['57', '66'])).
% 0.19/0.47  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('71', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.47        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47           (k1_zfmisc_1 @ 
% 0.19/0.47            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.19/0.47      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.19/0.47  thf('72', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.47        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47           (k1_zfmisc_1 @ 
% 0.19/0.47            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['56', '71'])).
% 0.19/0.47  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('76', plain,
% 0.19/0.47      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47        (k1_zfmisc_1 @ 
% 0.19/0.47         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.19/0.47      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.19/0.47  thf('77', plain,
% 0.19/0.47      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.19/0.47        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.47        | ~ (v2_funct_1 @ sk_C))),
% 0.19/0.47      inference('sup+', [status(thm)], ['55', '76'])).
% 0.19/0.47  thf('78', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.19/0.47      inference('sup+', [status(thm)], ['43', '44'])).
% 0.19/0.47  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('82', plain,
% 0.19/0.47      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.19/0.47  thf('83', plain, ($false), inference('demod', [status(thm)], ['54', '82'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
