%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGYOGa4lDg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:48 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 945 expanded)
%              Number of leaves         :   33 ( 305 expanded)
%              Depth                    :   30
%              Number of atoms          :  993 (12647 expanded)
%              Number of equality atoms :   36 ( 389 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','9','10'])).

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
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('13',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('16',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('23',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
        = ( k9_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['27','32'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( r1_tarski @ ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('35',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
        = ( k9_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X8: $i] :
      ( ( ( k10_relat_1 @ X8 @ ( k2_relat_1 @ X8 ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('43',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('47',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','49','50','51','52'])).

thf('54',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ( v5_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('61',plain,
    ( ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X30 ) @ X31 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['12','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['11','89','90'])).

thf('92',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','91'])).

thf('93',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('94',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('95',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('96',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( v1_funct_2 @ X30 @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('102',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['94','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['93','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['92','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gGYOGa4lDg
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 135 iterations in 0.095s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.56  thf(t31_funct_2, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.56       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.37/0.56         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.37/0.56           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.37/0.56           ( m1_subset_1 @
% 0.37/0.56             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.56          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.37/0.56            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.37/0.56              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.37/0.56              ( m1_subset_1 @
% 0.37/0.56                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.56        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.37/0.56        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.37/0.56         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf(dt_k2_funct_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 0.37/0.56          | ~ (v1_funct_1 @ X11)
% 0.37/0.56          | ~ (v1_relat_1 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.37/0.56         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.37/0.56         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(cc2_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.56          | (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf(fc6_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.56  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('11', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['4', '9', '10'])).
% 0.37/0.56  thf(t55_funct_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.56       ( ( v2_funct_1 @ A ) =>
% 0.37/0.56         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.37/0.56           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X18 : $i]:
% 0.37/0.56         (~ (v2_funct_1 @ X18)
% 0.37/0.56          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 0.37/0.56          | ~ (v1_funct_1 @ X18)
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 0.37/0.56          | ~ (v1_funct_1 @ X11)
% 0.37/0.56          | ~ (v1_relat_1 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.37/0.56          | ~ (v1_funct_1 @ X11)
% 0.37/0.56          | ~ (v1_relat_1 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.37/0.56          | ~ (v1_funct_1 @ X11)
% 0.37/0.56          | ~ (v1_relat_1 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.37/0.56          | ~ (v1_funct_1 @ X11)
% 0.37/0.56          | ~ (v1_relat_1 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(cc2_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.56         ((v4_relat_1 @ X19 @ X20)
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.56  thf('19', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf(t209_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.56       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.37/0.56          | ~ (v4_relat_1 @ X9 @ X10)
% 0.37/0.56          | ~ (v1_relat_1 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('23', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf(t148_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 0.37/0.56          | ~ (v1_relat_1 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('27', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.56         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.37/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('31', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('32', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.56  thf('33', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['27', '32'])).
% 0.37/0.56  thf(t152_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( v2_funct_1 @ B ) =>
% 0.37/0.56         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]:
% 0.37/0.56         (~ (v2_funct_1 @ X14)
% 0.37/0.56          | (r1_tarski @ (k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X15)) @ X15)
% 0.37/0.56          | ~ (v1_funct_1 @ X14)
% 0.37/0.56          | ~ (v1_relat_1 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (((r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 0.37/0.56          | ~ (v1_relat_1 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.56  thf(t169_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X8 : $i]:
% 0.37/0.56         (((k10_relat_1 @ X8 @ (k2_relat_1 @ X8)) = (k1_relat_1 @ X8))
% 0.37/0.56          | ~ (v1_relat_1 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.37/0.56            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.37/0.56          | ~ (v1_relat_1 @ X1)
% 0.37/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.37/0.56            (k9_relat_1 @ sk_C @ sk_A))
% 0.37/0.56            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['36', '39'])).
% 0.37/0.56  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('43', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf('44', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.37/0.56  thf('46', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.56  thf('49', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.56  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('53', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['35', '49', '50', '51', '52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X18 : $i]:
% 0.37/0.56         (~ (v2_funct_1 @ X18)
% 0.37/0.56          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 0.37/0.56          | ~ (v1_funct_1 @ X18)
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.37/0.56  thf(d19_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.37/0.56          | (v5_relat_1 @ X2 @ X3)
% 0.37/0.56          | ~ (v1_relat_1 @ X2))),
% 0.37/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.37/0.56          | ~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | ~ (v2_funct_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.37/0.56          | (v5_relat_1 @ (k2_funct_1 @ X0) @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.37/0.56        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['53', '56'])).
% 0.37/0.56  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.37/0.56        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['16', '61'])).
% 0.37/0.56  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('65', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         (~ (v5_relat_1 @ X2 @ X3)
% 0.37/0.56          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.37/0.56          | ~ (v1_relat_1 @ X2))),
% 0.37/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.56        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['15', '67'])).
% 0.37/0.56  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('71', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.37/0.56  thf(t4_funct_2, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.37/0.56         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.37/0.56           ( m1_subset_1 @
% 0.37/0.56             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      (![X30 : $i, X31 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.37/0.56          | (m1_subset_1 @ X30 @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X30) @ X31)))
% 0.37/0.56          | ~ (v1_funct_1 @ X30)
% 0.37/0.56          | ~ (v1_relat_1 @ X30))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.56        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.56        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56           (k1_zfmisc_1 @ 
% 0.37/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56           (k1_zfmisc_1 @ 
% 0.37/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.37/0.56        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '73'])).
% 0.37/0.56  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56         (k1_zfmisc_1 @ 
% 0.37/0.56          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.37/0.56        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56           (k1_zfmisc_1 @ 
% 0.37/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '77'])).
% 0.37/0.56  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('81', plain,
% 0.37/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.37/0.56  thf('82', plain,
% 0.37/0.56      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['12', '81'])).
% 0.37/0.56  thf('83', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.56  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('87', plain,
% 0.37/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.37/0.56  thf('88', plain,
% 0.37/0.56      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('89', plain,
% 0.37/0.56      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['87', '88'])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.37/0.56       ~
% 0.37/0.56       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.37/0.56       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('91', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['11', '89', '90'])).
% 0.37/0.56  thf('92', plain, (~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['1', '91'])).
% 0.37/0.56  thf('93', plain,
% 0.37/0.56      (![X18 : $i]:
% 0.37/0.56         (~ (v2_funct_1 @ X18)
% 0.37/0.56          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 0.37/0.56          | ~ (v1_funct_1 @ X18)
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.37/0.56  thf('94', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 0.37/0.56          | ~ (v1_funct_1 @ X11)
% 0.37/0.56          | ~ (v1_relat_1 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.56  thf('95', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.37/0.56  thf('96', plain,
% 0.37/0.56      (![X30 : $i, X31 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.37/0.56          | (v1_funct_2 @ X30 @ (k1_relat_1 @ X30) @ X31)
% 0.37/0.56          | ~ (v1_funct_1 @ X30)
% 0.37/0.56          | ~ (v1_relat_1 @ X30))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.37/0.56  thf('97', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.56        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.56        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.37/0.56  thf('98', plain,
% 0.37/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.37/0.56  thf('99', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.56          | (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.56  thf('100', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ 
% 0.37/0.56           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))
% 0.37/0.56        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['98', '99'])).
% 0.37/0.56  thf('101', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.56  thf('102', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['100', '101'])).
% 0.37/0.56  thf('103', plain,
% 0.37/0.56      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.56        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['97', '102'])).
% 0.37/0.56  thf('104', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['94', '103'])).
% 0.37/0.56  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('107', plain,
% 0.37/0.56      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.56        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.37/0.56  thf('108', plain,
% 0.37/0.56      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['93', '107'])).
% 0.37/0.56  thf('109', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.56  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('113', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.37/0.56  thf('114', plain, ($false), inference('demod', [status(thm)], ['92', '113'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
