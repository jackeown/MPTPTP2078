%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fg682ytY7J

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:50 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 311 expanded)
%              Number of leaves         :   26 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  803 (4586 expanded)
%              Number of equality atoms :   17 ( 116 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ X19 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','46','47','48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['12','52','53'])).

thf('55',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf('56',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('58',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('59',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( v1_funct_2 @ X18 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('71',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','67','68','69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['56','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['44','45'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['55','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fg682ytY7J
% 0.15/0.37  % Computer   : n006.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 12:15:08 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 74 iterations in 0.032s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.24/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.24/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.24/0.49  thf(t31_funct_2, conjecture,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.49       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.24/0.49         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.24/0.49           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.24/0.49           ( m1_subset_1 @
% 0.24/0.49             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.49          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.24/0.49            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.24/0.49              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.24/0.49              ( m1_subset_1 @
% 0.24/0.49                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.24/0.49  thf('0', plain,
% 0.24/0.49      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.49        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.24/0.49        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('1', plain,
% 0.24/0.49      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.24/0.49         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(cc2_relat_1, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ A ) =>
% 0.24/0.49       ( ![B:$i]:
% 0.24/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.24/0.49  thf('3', plain,
% 0.24/0.49      (![X3 : $i, X4 : $i]:
% 0.24/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.24/0.49          | (v1_relat_1 @ X3)
% 0.24/0.49          | ~ (v1_relat_1 @ X4))),
% 0.24/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.49  thf('4', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.49  thf(fc6_relat_1, axiom,
% 0.24/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.24/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.49  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf(dt_k2_funct_1, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.49       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.24/0.49         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.24/0.49  thf('7', plain,
% 0.24/0.49      (![X7 : $i]:
% 0.24/0.49         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.24/0.49          | ~ (v1_funct_1 @ X7)
% 0.24/0.49          | ~ (v1_relat_1 @ X7))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.24/0.49  thf('8', plain,
% 0.24/0.49      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.24/0.49         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('9', plain,
% 0.24/0.49      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.24/0.49         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.49  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('11', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.49  thf('12', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['6', '11'])).
% 0.24/0.49  thf(t55_funct_1, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.49       ( ( v2_funct_1 @ A ) =>
% 0.24/0.49         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.24/0.49           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.24/0.49  thf('13', plain,
% 0.24/0.49      (![X8 : $i]:
% 0.24/0.49         (~ (v2_funct_1 @ X8)
% 0.24/0.49          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.24/0.49          | ~ (v1_funct_1 @ X8)
% 0.24/0.49          | ~ (v1_relat_1 @ X8))),
% 0.24/0.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.24/0.49  thf('14', plain,
% 0.24/0.49      (![X7 : $i]:
% 0.24/0.49         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.24/0.49          | ~ (v1_funct_1 @ X7)
% 0.24/0.49          | ~ (v1_relat_1 @ X7))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.24/0.49  thf('15', plain,
% 0.24/0.49      (![X7 : $i]:
% 0.24/0.49         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.24/0.49          | ~ (v1_funct_1 @ X7)
% 0.24/0.49          | ~ (v1_relat_1 @ X7))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.24/0.49  thf('16', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(dt_k1_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.49  thf('17', plain,
% 0.24/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.49         ((m1_subset_1 @ (k1_relset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X9))
% 0.24/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.24/0.49  thf('18', plain,
% 0.24/0.49      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.49  thf('19', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.24/0.49  thf('20', plain,
% 0.24/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.49         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.24/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.24/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.24/0.49  thf('21', plain,
% 0.24/0.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.49  thf('22', plain,
% 0.24/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.49      inference('demod', [status(thm)], ['18', '21'])).
% 0.24/0.49  thf(t3_subset, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.49  thf('23', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.24/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.49  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.24/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.24/0.49  thf('25', plain,
% 0.24/0.49      (![X8 : $i]:
% 0.24/0.49         (~ (v2_funct_1 @ X8)
% 0.24/0.49          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.24/0.49          | ~ (v1_funct_1 @ X8)
% 0.24/0.49          | ~ (v1_relat_1 @ X8))),
% 0.24/0.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.24/0.49  thf(t4_funct_2, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.24/0.49         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.24/0.49           ( m1_subset_1 @
% 0.24/0.49             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.24/0.49  thf('26', plain,
% 0.24/0.49      (![X18 : $i, X19 : $i]:
% 0.24/0.49         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.24/0.49          | (m1_subset_1 @ X18 @ 
% 0.24/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ X19)))
% 0.24/0.49          | ~ (v1_funct_1 @ X18)
% 0.24/0.49          | ~ (v1_relat_1 @ X18))),
% 0.24/0.49      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.24/0.49  thf('27', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.24/0.49          | ~ (v1_relat_1 @ X0)
% 0.24/0.49          | ~ (v1_funct_1 @ X0)
% 0.24/0.49          | ~ (v2_funct_1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.24/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.49          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.24/0.49             (k1_zfmisc_1 @ 
% 0.24/0.49              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 0.24/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.49  thf('28', plain,
% 0.24/0.49      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49         (k1_zfmisc_1 @ 
% 0.24/0.49          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.24/0.49        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.49        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['24', '27'])).
% 0.24/0.49  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('32', plain,
% 0.24/0.49      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49         (k1_zfmisc_1 @ 
% 0.24/0.49          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.24/0.49        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.49      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.24/0.49  thf('33', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.49        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49           (k1_zfmisc_1 @ 
% 0.24/0.49            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.24/0.49      inference('sup-', [status(thm)], ['15', '32'])).
% 0.24/0.49  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('36', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.49        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49           (k1_zfmisc_1 @ 
% 0.24/0.49            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.24/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.24/0.49  thf('37', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49           (k1_zfmisc_1 @ 
% 0.24/0.49            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.24/0.49      inference('sup-', [status(thm)], ['14', '36'])).
% 0.24/0.49  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('40', plain,
% 0.24/0.49      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49        (k1_zfmisc_1 @ 
% 0.24/0.49         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.24/0.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.24/0.49  thf('41', plain,
% 0.24/0.49      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.24/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v2_funct_1 @ sk_C))),
% 0.24/0.49      inference('sup+', [status(thm)], ['13', '40'])).
% 0.24/0.49  thf('42', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.24/0.49  thf('43', plain,
% 0.24/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.24/0.49         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.24/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.24/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.24/0.49  thf('44', plain,
% 0.24/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.24/0.49  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('46', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.24/0.49      inference('sup+', [status(thm)], ['44', '45'])).
% 0.24/0.49  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('50', plain,
% 0.24/0.49      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.24/0.49      inference('demod', [status(thm)], ['41', '46', '47', '48', '49'])).
% 0.24/0.49  thf('51', plain,
% 0.24/0.49      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.24/0.49         <= (~
% 0.24/0.49             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('52', plain,
% 0.24/0.49      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.24/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.24/0.49  thf('53', plain,
% 0.24/0.49      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.24/0.49       ~
% 0.24/0.49       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.24/0.49       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('54', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.24/0.49      inference('sat_resolution*', [status(thm)], ['12', '52', '53'])).
% 0.24/0.49  thf('55', plain, (~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.24/0.49      inference('simpl_trail', [status(thm)], ['1', '54'])).
% 0.24/0.49  thf('56', plain,
% 0.24/0.49      (![X8 : $i]:
% 0.24/0.49         (~ (v2_funct_1 @ X8)
% 0.24/0.49          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.24/0.49          | ~ (v1_funct_1 @ X8)
% 0.24/0.49          | ~ (v1_relat_1 @ X8))),
% 0.24/0.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.24/0.49  thf('57', plain,
% 0.24/0.49      (![X7 : $i]:
% 0.24/0.49         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.24/0.49          | ~ (v1_funct_1 @ X7)
% 0.24/0.49          | ~ (v1_relat_1 @ X7))),
% 0.24/0.49      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.24/0.49  thf('58', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.24/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.24/0.49  thf('59', plain,
% 0.24/0.49      (![X8 : $i]:
% 0.24/0.49         (~ (v2_funct_1 @ X8)
% 0.24/0.49          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.24/0.49          | ~ (v1_funct_1 @ X8)
% 0.24/0.49          | ~ (v1_relat_1 @ X8))),
% 0.24/0.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.24/0.49  thf('60', plain,
% 0.24/0.49      (![X18 : $i, X19 : $i]:
% 0.24/0.49         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.24/0.49          | (v1_funct_2 @ X18 @ (k1_relat_1 @ X18) @ X19)
% 0.24/0.49          | ~ (v1_funct_1 @ X18)
% 0.24/0.49          | ~ (v1_relat_1 @ X18))),
% 0.24/0.49      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.24/0.49  thf('61', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.24/0.49          | ~ (v1_relat_1 @ X0)
% 0.24/0.49          | ~ (v1_funct_1 @ X0)
% 0.24/0.49          | ~ (v2_funct_1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.24/0.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.49          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.24/0.49             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.24/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.24/0.49  thf('62', plain,
% 0.24/0.49      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.24/0.49        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.49        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.49        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['58', '61'])).
% 0.24/0.49  thf('63', plain,
% 0.24/0.49      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49        (k1_zfmisc_1 @ 
% 0.24/0.49         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.24/0.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.24/0.49  thf('64', plain,
% 0.24/0.49      (![X3 : $i, X4 : $i]:
% 0.24/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.24/0.49          | (v1_relat_1 @ X3)
% 0.24/0.49          | ~ (v1_relat_1 @ X4))),
% 0.24/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.49  thf('65', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ 
% 0.24/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))
% 0.24/0.49        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.24/0.49  thf('66', plain,
% 0.24/0.49      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.24/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.49  thf('67', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.24/0.49      inference('demod', [status(thm)], ['65', '66'])).
% 0.24/0.49  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('71', plain,
% 0.24/0.49      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.24/0.49        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.49      inference('demod', [status(thm)], ['62', '67', '68', '69', '70'])).
% 0.24/0.49  thf('72', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.24/0.49      inference('sup-', [status(thm)], ['57', '71'])).
% 0.24/0.49  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('75', plain,
% 0.24/0.49      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.49        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.24/0.49      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.24/0.49  thf('76', plain,
% 0.24/0.49      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.24/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v2_funct_1 @ sk_C))),
% 0.24/0.49      inference('sup+', [status(thm)], ['56', '75'])).
% 0.24/0.49  thf('77', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.24/0.49      inference('sup+', [status(thm)], ['44', '45'])).
% 0.24/0.49  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('81', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.24/0.49      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.24/0.49  thf('82', plain, ($false), inference('demod', [status(thm)], ['55', '81'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
