%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5uBOOTC3ny

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 301 expanded)
%              Number of leaves         :   27 ( 102 expanded)
%              Depth                    :   15
%              Number of atoms          :  682 (4525 expanded)
%              Number of equality atoms :   21 ( 134 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ X3 )
        = ( k4_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('25',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v1_funct_2 @ X14 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( v1_funct_2 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('31',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('32',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('37',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['29','35','41','42'])).

thf('44',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['18','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','56','57'])).

thf('59',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','58'])).

thf('60',plain,(
    ! [X2: $i] :
      ( ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('61',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('62',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('67',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('69',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['49','50'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('73',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['59','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5uBOOTC3ny
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 60 iterations in 0.027s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.48  thf(t31_funct_2, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.20/0.48         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.20/0.48           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.20/0.48           ( m1_subset_1 @
% 0.20/0.48             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.20/0.48            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.20/0.48              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.20/0.48              ( m1_subset_1 @
% 0.20/0.48                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.48        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.20/0.48        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( v1_relat_1 @ C ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X5)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.48  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(d9_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X3 : $i]:
% 0.20/0.48         (~ (v2_funct_1 @ X3)
% 0.20/0.48          | ((k2_funct_1 @ X3) = (k4_relat_1 @ X3))
% 0.20/0.48          | ~ (v1_funct_1 @ X3)
% 0.20/0.48          | ~ (v1_relat_1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.48        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.20/0.48        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.20/0.48      inference('demod', [status(thm)], ['1', '9'])).
% 0.20/0.48  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(dt_k2_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.48         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X4 : $i]:
% 0.20/0.48         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.48          | ~ (v1_funct_1 @ X4)
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.20/0.48         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.20/0.48         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '16'])).
% 0.20/0.48  thf(t37_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X2 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 0.20/0.48          | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         ((v4_relat_1 @ X8 @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.48  thf('21', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf(d18_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v4_relat_1 @ X0 @ X1)
% 0.20/0.48          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('25', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X2 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.20/0.48          | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf(t4_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.48         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.20/0.48           ( m1_subset_1 @
% 0.20/0.48             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.20/0.48          | (v1_funct_2 @ X14 @ (k1_relat_1 @ X14) @ X15)
% 0.20/0.48          | ~ (v1_funct_1 @ X14)
% 0.20/0.48          | ~ (v1_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.20/0.48          | (v1_funct_2 @ (k4_relat_1 @ X0) @ 
% 0.20/0.48             (k1_relat_1 @ (k4_relat_1 @ X0)) @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ 
% 0.20/0.48         (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)
% 0.20/0.48        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.20/0.48        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.48  thf('30', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X4 : $i]:
% 0.20/0.48         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.48          | ~ (v1_funct_1 @ X4)
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.48      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.48  thf('36', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X4 : $i]:
% 0.20/0.48         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.20/0.48          | ~ (v1_funct_1 @ X4)
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.48      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.48  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ 
% 0.20/0.48        (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '35', '41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup+', [status(thm)], ['18', '43'])).
% 0.20/0.48  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['46', '51'])).
% 0.20/0.48  thf('53', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.20/0.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.20/0.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('56', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['52', '55'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.20/0.48       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.20/0.48       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['17', '56', '57'])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['10', '58'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (![X2 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X2) = (k1_relat_1 @ (k4_relat_1 @ X2)))
% 0.20/0.48          | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf('61', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (![X2 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X2) = (k2_relat_1 @ (k4_relat_1 @ X2)))
% 0.20/0.48          | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.20/0.48          | (m1_subset_1 @ X14 @ 
% 0.20/0.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X14) @ X15)))
% 0.20/0.48          | ~ (v1_funct_1 @ X14)
% 0.20/0.48          | ~ (v1_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.20/0.48          | (m1_subset_1 @ (k4_relat_1 @ X0) @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ X1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ 
% 0.20/0.48          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 0.20/0.48        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.20/0.48        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['61', '64'])).
% 0.20/0.48  thf('66', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.48  thf('67', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.48  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup+', [status(thm)], ['60', '69'])).
% 0.20/0.48  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('73', plain,
% 0.20/0.48      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.20/0.48  thf('74', plain, ($false), inference('demod', [status(thm)], ['59', '73'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
