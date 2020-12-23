%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RkgtpVYTQF

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 191 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  998 (3035 expanded)
%              Number of equality atoms :   69 ( 185 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k7_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k9_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k7_relset_1 @ X25 @ X26 @ X27 @ X25 )
        = ( k2_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('7',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X8 @ X6 )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k8_relset_1 @ X25 @ X26 @ X27 @ X26 )
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('23',plain,
    ( ( k8_relset_1 @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_relset_1 @ X4 @ X5 @ X3 )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['23','26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_relset_1 @ X4 @ X5 @ X3 )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4','12','15','30','33'])).

thf('35',plain,
    ( $false
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k7_relset_1 @ X25 @ X26 @ X27 @ X25 )
        = ( k2_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('42',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k7_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k9_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X8 @ X6 )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k8_relset_1 @ X25 @ X26 @ X27 @ X26 )
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('52',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('55',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('58',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('61',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf('65',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,(
    ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
 != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['35','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RkgtpVYTQF
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:18:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 60 iterations in 0.023s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(t39_relset_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.47       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.20/0.47           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.47         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.20/0.47           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.47          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.20/0.47              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.47            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.20/0.47              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.20/0.47        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.47            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.47          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.20/0.47          | ((k7_relset_1 @ X10 @ X11 @ X9 @ X12) = (k9_relat_1 @ X9 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t38_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.47         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.47         (((k7_relset_1 @ X25 @ X26 @ X27 @ X25)
% 0.20/0.47            = (k2_relset_1 @ X25 @ X26 @ X27))
% 0.20/0.47          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 0.20/0.47         = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (((k2_relset_1 @ X7 @ X8 @ X6) = (k2_relat_1 @ X6))
% 0.20/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, (((k9_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.47          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t14_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.20/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 0.20/0.47          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.20/0.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.20/0.47          | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ 
% 0.20/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.47         (((k8_relset_1 @ X25 @ X26 @ X27 @ X26)
% 0.20/0.47            = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.20/0.47          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((k8_relset_1 @ sk_B @ (k2_relat_1 @ sk_C) @ sk_C @ (k2_relat_1 @ sk_C))
% 0.20/0.47         = (k1_relset_1 @ sk_B @ (k2_relat_1 @ sk_C) @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ 
% 0.20/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.47          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k8_relset_1 @ sk_B @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 0.20/0.47           = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ 
% 0.20/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (((k1_relset_1 @ X4 @ X5 @ X3) = (k1_relat_1 @ X3))
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (((k1_relset_1 @ sk_B @ (k2_relat_1 @ sk_C) @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '26', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (((k1_relset_1 @ X4 @ X5 @ X3) = (k1_relat_1 @ X3))
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('demod', [status(thm)], ['1', '4', '12', '15', '30', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (($false)
% 0.20/0.47         <= (~
% 0.20/0.47             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.47                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.47  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t13_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.20/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.20/0.47          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.20/0.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.20/0.47          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ 
% 0.20/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.47         (((k7_relset_1 @ X25 @ X26 @ X27 @ X25)
% 0.20/0.47            = (k2_relset_1 @ X25 @ X26 @ X27))
% 0.20/0.47          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ (k1_relat_1 @ sk_C))
% 0.20/0.47         = (k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ 
% 0.20/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.20/0.47          | ((k7_relset_1 @ X10 @ X11 @ X9 @ X12) = (k9_relat_1 @ X9 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k7_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.20/0.47           = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ 
% 0.20/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (((k2_relset_1 @ X7 @ X8 @ X6) = (k2_relat_1 @ X6))
% 0.20/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['42', '45', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.47         (((k8_relset_1 @ X25 @ X26 @ X27 @ X26)
% 0.20/0.47            = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.20/0.47          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.47      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.20/0.47         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('55', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('57', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('58', plain,
% 0.20/0.47      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('59', plain,
% 0.20/0.47      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.47  thf('60', plain,
% 0.20/0.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('61', plain,
% 0.20/0.47      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47          != (k2_relat_1 @ sk_C)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.47  thf('62', plain,
% 0.20/0.47      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.20/0.47          != (k2_relat_1 @ sk_C)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['56', '61'])).
% 0.20/0.47  thf('63', plain,
% 0.20/0.47      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['55', '62'])).
% 0.20/0.47  thf('64', plain,
% 0.20/0.47      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['49', '63'])).
% 0.20/0.47  thf('65', plain,
% 0.20/0.47      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['64'])).
% 0.20/0.47  thf('66', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.47          = (k1_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.20/0.47       ~
% 0.20/0.47       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.47          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('67', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.47          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.47          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.20/0.47  thf('68', plain, ($false),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['35', '67'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
