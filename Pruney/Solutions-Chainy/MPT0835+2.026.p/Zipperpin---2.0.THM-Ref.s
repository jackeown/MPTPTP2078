%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JHS265A0rV

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 133 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  824 (2224 expanded)
%              Number of equality atoms :   66 ( 148 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t39_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
            = ( k2_relset_1 @ B @ A @ C ) )
          & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
            = ( k1_relset_1 @ B @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_relset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k8_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k10_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k7_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k9_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X1 ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k7_relset_1 @ X19 @ X20 @ X21 @ X19 )
        = ( k2_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('19',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('22',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['7'])).

thf('25',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['7'])).

thf('39',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['14','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k8_relset_1 @ X19 @ X20 @ X21 @ X20 )
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('43',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','46'])).

thf('48',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('50',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JHS265A0rV
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:04:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 32 iterations in 0.010s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(t146_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.47  thf(t39_relset_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.47       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.47           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.47         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.47           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.47          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.47              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.47            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.47              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.21/0.47          | ((k8_relset_1 @ X16 @ X17 @ X15 @ X18) = (k10_relat_1 @ X15 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.47          | ((k7_relset_1 @ X12 @ X13 @ X11 @ X14) = (k9_relat_1 @ X11 @ X14)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.21/0.47        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.21/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47          != (k2_relat_1 @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.47          != (k2_relat_1 @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '13'])).
% 0.21/0.47  thf(t169_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X1 : $i]:
% 0.21/0.47         (((k10_relat_1 @ X1 @ (k2_relat_1 @ X1)) = (k1_relat_1 @ X1))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t38_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.47         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.47         (((k7_relset_1 @ X19 @ X20 @ X21 @ X19)
% 0.21/0.47            = (k2_relset_1 @ X19 @ X20 @ X21))
% 0.21/0.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 0.21/0.47         = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('22', plain, (((k9_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['7'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.47          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.21/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.47          != (k1_relat_1 @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('demod', [status(thm)], ['25', '28'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.47          != (k1_relat_1 @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '31'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(cc1_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( v1_relat_1 @ C ) ))).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         ((v1_relat_1 @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.47  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.21/0.47         <= (~
% 0.21/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.47      inference('demod', [status(thm)], ['32', '35'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.21/0.47       ~
% 0.21/0.47       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.47          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['7'])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (~
% 0.21/0.47       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.47          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.47          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.47         != (k2_relat_1 @ sk_C))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['14', '39'])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.47         (((k8_relset_1 @ X19 @ X20 @ X21 @ X20)
% 0.21/0.47            = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.21/0.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.21/0.47         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.47  thf('46', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['40', '46'])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '47'])).
% 0.21/0.47  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.47  thf('50', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.47  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
