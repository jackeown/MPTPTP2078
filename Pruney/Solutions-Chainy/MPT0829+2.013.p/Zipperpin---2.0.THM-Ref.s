%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uG85AfPsjk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 149 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  663 (1297 expanded)
%              Number of equality atoms :   49 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t32_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
       => ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) )
          & ( B
            = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
         => ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) )
            & ( B
              = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ ( k6_relat_1 @ X24 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( ( k6_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('36',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('38',plain,
    ( ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k6_relat_1 @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','27','42'])).

thf('44',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('56',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X32 ) @ X33 )
      | ( r1_tarski @ X32 @ ( k1_relset_1 @ X34 @ X35 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['48'])).

thf('60',plain,(
    r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['48'])).

thf('62',plain,(
    sk_B
 != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['53','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uG85AfPsjk
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 99 iterations in 0.047s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(t32_relset_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.19/0.50         ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 0.19/0.50           ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.50        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.19/0.50            ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 0.19/0.50              ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t32_relset_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc2_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.50         ((v5_relat_1 @ X26 @ X28)
% 0.19/0.50          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.50  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf(d19_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         (~ (v5_relat_1 @ X11 @ X12)
% 0.19/0.50          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.19/0.50          | ~ (v1_relat_1 @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc2_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.19/0.50          | (v1_relat_1 @ X9)
% 0.19/0.50          | ~ (v1_relat_1 @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.50  thf(fc6_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.50  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.19/0.50      inference('demod', [status(thm)], ['4', '9'])).
% 0.19/0.50  thf(t71_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.50  thf('11', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf(t97_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.50         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X22 : $i, X23 : $i]:
% 0.19/0.50         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.19/0.50          | ((k7_relat_1 @ X22 @ X23) = (X22))
% 0.19/0.50          | ~ (v1_relat_1 @ X22))),
% 0.19/0.50      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.19/0.50  thf('14', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf(t94_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X20 : $i, X21 : $i]:
% 0.19/0.50         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 0.19/0.50          | ~ (v1_relat_1 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.50  thf(t43_funct_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X24 : $i, X25 : $i]:
% 0.19/0.50         ((k5_relat_1 @ (k6_relat_1 @ X25) @ (k6_relat_1 @ X24))
% 0.19/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X24 @ X25)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.50            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.50          | ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) = (k6_relat_1 @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['15', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (((k6_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))
% 0.19/0.50         = (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '21'])).
% 0.19/0.50  thf(commutativity_k2_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.50  thf(t12_setfam_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]:
% 0.19/0.50         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.19/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]:
% 0.19/0.50         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.19/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t25_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( v1_relat_1 @ B ) =>
% 0.19/0.50           ( ( r1_tarski @ A @ B ) =>
% 0.19/0.50             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.50               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X16)
% 0.19/0.50          | (r1_tarski @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 0.19/0.50          | ~ (r1_tarski @ X17 @ X16)
% 0.19/0.50          | ~ (v1_relat_1 @ X17))),
% 0.19/0.50      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.19/0.50        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_B)) @ (k2_relat_1 @ sk_C))
% 0.19/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.50  thf('31', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.50  thf('32', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf('34', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (((k7_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))
% 0.19/0.50         = (k6_relat_1 @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (((k6_relat_1 @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.19/0.50         = (k6_relat_1 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('39', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (((k1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.19/0.50         = (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['38', '39'])).
% 0.19/0.50  thf('41', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('42', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.19/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (((k6_relat_1 @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.19/0.50      inference('demod', [status(thm)], ['22', '27', '42'])).
% 0.19/0.50  thf('44', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 0.19/0.50      inference('sup+', [status(thm)], ['43', '44'])).
% 0.19/0.50  thf('46', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('47', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.19/0.50        | ((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      ((((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.19/0.50         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.19/0.50      inference('split', [status(esa)], ['48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.50         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.19/0.50          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      ((((sk_B) != (k2_relat_1 @ sk_C)))
% 0.19/0.50         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.19/0.50      inference('demod', [status(thm)], ['49', '52'])).
% 0.19/0.50  thf('54', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t30_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.19/0.50         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.19/0.50           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.50         (~ (r1_tarski @ (k6_relat_1 @ X32) @ X33)
% 0.19/0.50          | (r1_tarski @ X32 @ (k1_relset_1 @ X34 @ X35 @ X33))
% 0.19/0.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.19/0.50      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ X0 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.19/0.50          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.50  thf('58', plain, ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['54', '57'])).
% 0.19/0.50  thf('59', plain,
% 0.19/0.50      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.19/0.50         <= (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.19/0.50      inference('split', [status(esa)], ['48'])).
% 0.19/0.50  thf('60', plain, (((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.50  thf('61', plain,
% 0.19/0.50      (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.19/0.50       ~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.50      inference('split', [status(esa)], ['48'])).
% 0.19/0.50  thf('62', plain, (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.19/0.50  thf('63', plain, (((sk_B) != (k2_relat_1 @ sk_C))),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['53', '62'])).
% 0.19/0.50  thf('64', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['47', '63'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
