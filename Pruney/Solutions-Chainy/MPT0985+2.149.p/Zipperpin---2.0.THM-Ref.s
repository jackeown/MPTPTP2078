%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ITYieF8zsH

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:48 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 659 expanded)
%              Number of leaves         :   34 ( 218 expanded)
%              Depth                    :   17
%              Number of atoms          :  872 (9422 expanded)
%              Number of equality atoms :   42 ( 296 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','11'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('26',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( r1_tarski @ ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('32',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('39',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('45',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('46',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('47',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('48',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('60',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('61',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('62',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('67',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('68',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('69',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('76',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','58','59','65','66','72','73','74','75'])).

thf('77',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','80','81'])).

thf('83',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','82'])).

thf('84',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('85',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k1_relat_1 @ X15 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('86',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ( v1_funct_2 @ X22 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('90',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('91',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('92',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('93',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('94',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('95',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('99',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94','95','96','97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['83','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ITYieF8zsH
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 95 iterations in 0.055s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.35/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.35/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.55  thf(t31_funct_2, conjecture,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.55       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.35/0.55         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.35/0.55           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.35/0.55           ( m1_subset_1 @
% 0.35/0.55             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.55          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.35/0.55            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.35/0.55              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.35/0.55              ( m1_subset_1 @
% 0.35/0.55                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.55        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.35/0.55        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.35/0.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(cc2_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.35/0.55          | (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.55  thf(fc6_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.55  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf(d9_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      (![X11 : $i]:
% 0.35/0.55         (~ (v2_funct_1 @ X11)
% 0.35/0.55          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.35/0.55          | ~ (v1_funct_1 @ X11)
% 0.35/0.55          | ~ (v1_relat_1 @ X11))),
% 0.35/0.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.55        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.35/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.55  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('11', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.35/0.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['1', '11'])).
% 0.35/0.55  thf(dt_k2_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.35/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (![X12 : $i]:
% 0.35/0.55         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.35/0.55          | ~ (v1_funct_1 @ X12)
% 0.35/0.55          | ~ (v1_relat_1 @ X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.35/0.55         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.35/0.55         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.55  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('18', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.55      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.35/0.55  thf(t169_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (![X7 : $i]:
% 0.35/0.55         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 0.35/0.55          | ~ (v1_relat_1 @ X7))),
% 0.35/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(cc2_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.55         ((v4_relat_1 @ X16 @ X17)
% 0.35/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.55  thf('22', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.35/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf(t209_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.35/0.55       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      (![X8 : $i, X9 : $i]:
% 0.35/0.55         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.35/0.55          | ~ (v4_relat_1 @ X8 @ X9)
% 0.35/0.55          | ~ (v1_relat_1 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.55  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('26', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf(t148_relat_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ B ) =>
% 0.38/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i]:
% 0.38/0.55         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.38/0.55          | ~ (v1_relat_1 @ X5))),
% 0.38/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.55  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('30', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.55  thf(t152_funct_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.55       ( ( v2_funct_1 @ B ) =>
% 0.38/0.55         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i]:
% 0.38/0.55         (~ (v2_funct_1 @ X13)
% 0.38/0.55          | (r1_tarski @ (k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X14)) @ X14)
% 0.38/0.55          | ~ (v1_funct_1 @ X13)
% 0.38/0.55          | ~ (v1_relat_1 @ X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) @ sk_A)
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.55  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('35', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) @ sk_A)),
% 0.38/0.55      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.55      inference('sup+', [status(thm)], ['19', '36'])).
% 0.38/0.55  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('39', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.38/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.55  thf(t55_funct_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.55       ( ( v2_funct_1 @ A ) =>
% 0.38/0.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (![X15 : $i]:
% 0.38/0.55         (~ (v2_funct_1 @ X15)
% 0.38/0.55          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 0.38/0.55          | ~ (v1_funct_1 @ X15)
% 0.38/0.55          | ~ (v1_relat_1 @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.55  thf(t4_funct_2, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.38/0.55         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.38/0.55           ( m1_subset_1 @
% 0.38/0.55             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X22 : $i, X23 : $i]:
% 0.38/0.55         (~ (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.38/0.55          | (m1_subset_1 @ X22 @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X22) @ X23)))
% 0.38/0.55          | ~ (v1_funct_1 @ X22)
% 0.38/0.55          | ~ (v1_relat_1 @ X22))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.38/0.55          | ~ (v1_relat_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (v2_funct_1 @ X0)
% 0.38/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.55          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.55         (k1_zfmisc_1 @ 
% 0.38/0.55          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.38/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['39', '42'])).
% 0.38/0.55  thf('44', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('45', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('46', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      (![X15 : $i]:
% 0.38/0.55         (~ (v2_funct_1 @ X15)
% 0.38/0.55          | ((k2_relat_1 @ X15) = (k1_relat_1 @ (k2_funct_1 @ X15)))
% 0.38/0.55          | ~ (v1_funct_1 @ X15)
% 0.38/0.55          | ~ (v1_relat_1 @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.55      inference('sup+', [status(thm)], ['46', '47'])).
% 0.38/0.55  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.55      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.38/0.55  thf('53', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.55  thf('54', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.55         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.38/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.55  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.38/0.55      inference('sup+', [status(thm)], ['55', '56'])).
% 0.38/0.55  thf('58', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.55      inference('demod', [status(thm)], ['52', '57'])).
% 0.38/0.55  thf('59', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('60', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('61', plain,
% 0.38/0.55      (![X12 : $i]:
% 0.38/0.55         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.38/0.55          | ~ (v1_funct_1 @ X12)
% 0.38/0.55          | ~ (v1_relat_1 @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.55      inference('sup+', [status(thm)], ['60', '61'])).
% 0.38/0.55  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('65', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.38/0.55  thf('66', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('67', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('68', plain,
% 0.38/0.55      (![X12 : $i]:
% 0.38/0.55         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.38/0.55          | ~ (v1_funct_1 @ X12)
% 0.38/0.55          | ~ (v1_relat_1 @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.55  thf('69', plain,
% 0.38/0.55      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.55      inference('sup+', [status(thm)], ['67', '68'])).
% 0.38/0.55  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('72', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.38/0.55  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('76', plain,
% 0.38/0.55      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['43', '44', '45', '58', '59', '65', '66', '72', '73', '74', 
% 0.38/0.55                 '75'])).
% 0.38/0.55  thf('77', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('78', plain,
% 0.38/0.55      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('79', plain,
% 0.38/0.55      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['77', '78'])).
% 0.38/0.55  thf('80', plain,
% 0.38/0.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['76', '79'])).
% 0.38/0.55  thf('81', plain,
% 0.38/0.55      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.38/0.55       ~
% 0.38/0.55       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.38/0.55       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('82', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['18', '80', '81'])).
% 0.38/0.55  thf('83', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['12', '82'])).
% 0.38/0.55  thf('84', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.38/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.55  thf('85', plain,
% 0.38/0.55      (![X15 : $i]:
% 0.38/0.55         (~ (v2_funct_1 @ X15)
% 0.38/0.55          | ((k1_relat_1 @ X15) = (k2_relat_1 @ (k2_funct_1 @ X15)))
% 0.38/0.55          | ~ (v1_funct_1 @ X15)
% 0.38/0.55          | ~ (v1_relat_1 @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.55  thf('86', plain,
% 0.38/0.55      (![X22 : $i, X23 : $i]:
% 0.38/0.55         (~ (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.38/0.55          | (v1_funct_2 @ X22 @ (k1_relat_1 @ X22) @ X23)
% 0.38/0.55          | ~ (v1_funct_1 @ X22)
% 0.38/0.55          | ~ (v1_relat_1 @ X22))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.38/0.55  thf('87', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.38/0.55          | ~ (v1_relat_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (v2_funct_1 @ X0)
% 0.38/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.38/0.55             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['85', '86'])).
% 0.38/0.55  thf('88', plain,
% 0.38/0.55      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.55         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.38/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.55      inference('sup-', [status(thm)], ['84', '87'])).
% 0.38/0.55  thf('89', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('90', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('91', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.55      inference('demod', [status(thm)], ['52', '57'])).
% 0.38/0.55  thf('92', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('93', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.38/0.55  thf('94', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.55  thf('95', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.38/0.55  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('99', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['88', '89', '90', '91', '92', '93', '94', '95', '96', '97', 
% 0.38/0.55                 '98'])).
% 0.38/0.55  thf('100', plain, ($false), inference('demod', [status(thm)], ['83', '99'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
