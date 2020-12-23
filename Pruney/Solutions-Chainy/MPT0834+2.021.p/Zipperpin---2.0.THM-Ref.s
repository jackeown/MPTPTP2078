%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hZQ6ouf1kG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 308 expanded)
%              Number of leaves         :   36 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  870 (3624 expanded)
%              Number of equality atoms :   72 ( 248 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t38_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( ( k7_relset_1 @ A @ B @ C @ A )
            = ( k2_relset_1 @ A @ B @ C ) )
          & ( ( k8_relset_1 @ A @ B @ C @ B )
            = ( k1_relset_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_relset_1])).

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','23','26'])).

thf('28',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['5','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('33',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k8_relset_1 @ X38 @ X39 @ X37 @ X40 )
        = ( k10_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k8_relat_1 @ X10 @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( ( k8_relat_1 @ X0 @ ( k7_relat_1 @ sk_C @ sk_A ) )
        = ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('48',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('49',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( ( k8_relat_1 @ X0 @ sk_C )
        = sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf('53',plain,
    ( ( k8_relat_1 @ sk_B @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['41','52'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X7 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k10_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ X13 @ ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','57'])).

thf('59',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X15: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k2_relat_1 @ X15 ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('66',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('68',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('69',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('71',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','69','70'])).

thf('72',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','34','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hZQ6ouf1kG
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 80 iterations in 0.065s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(t38_relset_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.53         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.53            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.53        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.53         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.20/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.53  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.20/0.53          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.53         ((v4_relat_1 @ X21 @ X22)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('13', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf(t209_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.20/0.53          | ~ (v4_relat_1 @ X16 @ X17)
% 0.20/0.53          | ~ (v1_relat_1 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( v1_relat_1 @ C ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((v1_relat_1 @ X18)
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.53  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf(t148_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('23', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.53         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.20/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '23', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.53       ~
% 0.20/0.53       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.53          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['5', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.20/0.53          | ((k8_relset_1 @ X38 @ X39 @ X37 @ X40) = (k10_relat_1 @ X37 @ X40)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k2_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('41', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.53  thf(t125_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.53         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.20/0.53          | ((k8_relat_1 @ X10 @ X9) = (X9))
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.53          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.53              = (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.20/0.53          | ((k8_relat_1 @ X0 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.53              = (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.53          | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '45'])).
% 0.20/0.53  thf('47', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('48', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('49', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.20/0.53          | ((k8_relat_1 @ X0 @ sk_C) = (sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['46', '47', '48', '49', '50', '51'])).
% 0.20/0.53  thf('53', plain, (((k8_relat_1 @ sk_B @ sk_C) = (sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '52'])).
% 0.20/0.53  thf(t119_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.20/0.53         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (((k2_relat_1 @ (k8_relat_1 @ X8 @ X7))
% 0.20/0.53            = (k3_xboole_0 @ (k2_relat_1 @ X7) @ X8))
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.20/0.53  thf(t168_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( k10_relat_1 @ B @ A ) =
% 0.20/0.53         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X13 @ X14)
% 0.20/0.53            = (k10_relat_1 @ X13 @ (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14)))
% 0.20/0.53          | ~ (v1_relat_1 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X0 @ X1)
% 0.20/0.53            = (k10_relat_1 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0))))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k10_relat_1 @ X0 @ X1)
% 0.20/0.53              = (k10_relat_1 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.20/0.53          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['53', '57'])).
% 0.20/0.53  thf('59', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.53  thf(t169_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X15 : $i]:
% 0.20/0.53         (((k10_relat_1 @ X15 @ (k2_relat_1 @ X15)) = (k1_relat_1 @ X15))
% 0.20/0.53          | ~ (v1_relat_1 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.53            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.53        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.20/0.53            (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.53            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '62'])).
% 0.20/0.53  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('66', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('67', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('68', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['63', '64', '65', '66', '67', '68'])).
% 0.20/0.53  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('71', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['58', '69', '70'])).
% 0.20/0.53  thf('72', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '34', '71'])).
% 0.20/0.53  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
