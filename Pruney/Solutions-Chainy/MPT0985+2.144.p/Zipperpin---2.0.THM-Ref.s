%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jf0fHj4XTW

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 350 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :   15
%              Number of atoms          :  685 (4752 expanded)
%              Number of equality atoms :   21 ( 134 expanded)
%              Maximal formula depth    :   13 (   5 average)

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

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','11'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v1_funct_2 @ X15 @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( v1_funct_2 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('32',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('33',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('38',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('39',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('44',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['30','36','42','43'])).

thf('45',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('52',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['45','50','51'])).

thf('53',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

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
    inference('sat_resolution*',[status(thm)],['18','56','57'])).

thf('59',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['12','58'])).

thf('60',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('61',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('62',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X15 ) @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    inference(demod,[status(thm)],['33','34','35'])).

thf('67',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

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
    inference('sup+',[status(thm)],['48','49'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('73',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['59','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jf0fHj4XTW
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 59 iterations in 0.024s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(t31_funct_2, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.21/0.49         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.21/0.49           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.21/0.49           ( m1_subset_1 @
% 0.21/0.49             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.21/0.49            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.21/0.49              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.21/0.49              ( m1_subset_1 @
% 0.21/0.49                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.49        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.49        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.21/0.49         <= (~
% 0.21/0.49             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc2_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.49          | (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(fc6_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.49  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(d9_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         (~ (v2_funct_1 @ X7)
% 0.21/0.49          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ~ (v1_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.21/0.49        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.21/0.49         <= (~
% 0.21/0.49             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '11'])).
% 0.21/0.49  thf(dt_k2_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.49         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X8 : $i]:
% 0.21/0.49         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.21/0.49          | ~ (v1_funct_1 @ X8)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.49         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.21/0.49         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf(t37_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.21/0.49         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         (((k2_relat_1 @ X6) = (k1_relat_1 @ (k4_relat_1 @ X6)))
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         ((v4_relat_1 @ X9 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.49  thf('22', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf(d18_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (v4_relat_1 @ X2 @ X3)
% 0.21/0.49          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('26', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X6) = (k2_relat_1 @ (k4_relat_1 @ X6)))
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.49  thf(t4_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.49         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.21/0.49           ( m1_subset_1 @
% 0.21/0.49             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.21/0.49          | (v1_funct_2 @ X15 @ (k1_relat_1 @ X15) @ X16)
% 0.21/0.49          | ~ (v1_funct_1 @ X15)
% 0.21/0.49          | ~ (v1_relat_1 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.21/0.49          | (v1_funct_2 @ (k4_relat_1 @ X0) @ 
% 0.21/0.49             (k1_relat_1 @ (k4_relat_1 @ X0)) @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ 
% 0.21/0.49         (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)
% 0.21/0.49        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.21/0.49        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.49  thf('31', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X8 : $i]:
% 0.21/0.49         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.21/0.49          | ~ (v1_funct_1 @ X8)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.49  thf('37', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X8 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.21/0.49          | ~ (v1_funct_1 @ X8)
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.49  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ 
% 0.21/0.49        (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '36', '42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['19', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('52', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['45', '50', '51'])).
% 0.21/0.49  thf('53', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.21/0.49         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.21/0.49         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('56', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '55'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.21/0.49       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.21/0.49       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['18', '56', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['12', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         (((k2_relat_1 @ X6) = (k1_relat_1 @ (k4_relat_1 @ X6)))
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.49  thf('61', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (![X6 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X6) = (k2_relat_1 @ (k4_relat_1 @ X6)))
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.21/0.49          | (m1_subset_1 @ X15 @ 
% 0.21/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X15) @ X16)))
% 0.21/0.49          | ~ (v1_funct_1 @ X15)
% 0.21/0.49          | ~ (v1_relat_1 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 0.21/0.49          | (m1_subset_1 @ (k4_relat_1 @ X0) @ 
% 0.21/0.49             (k1_zfmisc_1 @ 
% 0.21/0.49              (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ X1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.21/0.49         (k1_zfmisc_1 @ 
% 0.21/0.49          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 0.21/0.49        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.21/0.49        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['61', '64'])).
% 0.21/0.49  thf('66', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.49  thf('67', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.49  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.21/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['60', '69'])).
% 0.21/0.49  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.21/0.49  thf('74', plain, ($false), inference('demod', [status(thm)], ['59', '73'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
