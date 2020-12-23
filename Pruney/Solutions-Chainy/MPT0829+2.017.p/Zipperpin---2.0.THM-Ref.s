%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aYb6ALhJy6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:11 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 355 expanded)
%              Number of leaves         :   31 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  697 (3239 expanded)
%              Number of equality atoms :   36 ( 125 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( ( r1_tarski @ X19 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('31',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('33',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('42',plain,(
    v1_relat_1 @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('43',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','42','43'])).

thf('45',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,
    ( sk_B
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['5','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('57',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','44'])).

thf('58',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('60',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ ( k6_relat_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('62',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('65',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','44'])).

thf('67',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_B @ ( k6_relat_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['55','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aYb6ALhJy6
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.90/2.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.90/2.09  % Solved by: fo/fo7.sh
% 1.90/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.90/2.09  % done 4753 iterations in 1.635s
% 1.90/2.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.90/2.09  % SZS output start Refutation
% 1.90/2.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.90/2.09  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.90/2.09  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.90/2.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.90/2.09  thf(sk_B_type, type, sk_B: $i).
% 1.90/2.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.90/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.90/2.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.90/2.09  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.90/2.09  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.90/2.09  thf(sk_C_type, type, sk_C: $i).
% 1.90/2.09  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.90/2.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.90/2.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.90/2.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.90/2.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.90/2.09  thf(t32_relset_1, conjecture,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.90/2.09       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 1.90/2.09         ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 1.90/2.09           ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ))).
% 1.90/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.90/2.09    (~( ![A:$i,B:$i,C:$i]:
% 1.90/2.09        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.90/2.09          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 1.90/2.09            ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 1.90/2.09              ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) )),
% 1.90/2.09    inference('cnf.neg', [status(esa)], [t32_relset_1])).
% 1.90/2.09  thf('0', plain,
% 1.90/2.09      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))
% 1.90/2.09        | ((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf('1', plain,
% 1.90/2.09      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 1.90/2.09         <= (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.90/2.09      inference('split', [status(esa)], ['0'])).
% 1.90/2.09  thf('2', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(redefinition_k1_relset_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.90/2.09       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.90/2.09  thf('3', plain,
% 1.90/2.09      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.90/2.09         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.90/2.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.90/2.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.90/2.09  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup-', [status(thm)], ['2', '3'])).
% 1.90/2.09  thf('5', plain,
% 1.90/2.09      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C)))
% 1.90/2.09         <= (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.90/2.09      inference('demod', [status(thm)], ['1', '4'])).
% 1.90/2.09  thf('6', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(cc2_relset_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.90/2.09       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.90/2.09  thf('7', plain,
% 1.90/2.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.90/2.09         ((v5_relat_1 @ X22 @ X24)
% 1.90/2.09          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.90/2.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.90/2.09  thf('8', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 1.90/2.09      inference('sup-', [status(thm)], ['6', '7'])).
% 1.90/2.09  thf(d19_relat_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( v1_relat_1 @ B ) =>
% 1.90/2.09       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.90/2.09  thf('9', plain,
% 1.90/2.09      (![X15 : $i, X16 : $i]:
% 1.90/2.09         (~ (v5_relat_1 @ X15 @ X16)
% 1.90/2.09          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 1.90/2.09          | ~ (v1_relat_1 @ X15))),
% 1.90/2.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.90/2.09  thf('10', plain,
% 1.90/2.09      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.90/2.09      inference('sup-', [status(thm)], ['8', '9'])).
% 1.90/2.09  thf('11', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(cc2_relat_1, axiom,
% 1.90/2.09    (![A:$i]:
% 1.90/2.09     ( ( v1_relat_1 @ A ) =>
% 1.90/2.09       ( ![B:$i]:
% 1.90/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.90/2.09  thf('12', plain,
% 1.90/2.09      (![X13 : $i, X14 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.90/2.09          | (v1_relat_1 @ X13)
% 1.90/2.09          | ~ (v1_relat_1 @ X14))),
% 1.90/2.09      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.90/2.09  thf('13', plain,
% 1.90/2.09      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup-', [status(thm)], ['11', '12'])).
% 1.90/2.09  thf(fc6_relat_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.90/2.09  thf('14', plain,
% 1.90/2.09      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 1.90/2.09      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.90/2.09  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 1.90/2.09      inference('demod', [status(thm)], ['13', '14'])).
% 1.90/2.09  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 1.90/2.09      inference('demod', [status(thm)], ['10', '15'])).
% 1.90/2.09  thf(d10_xboole_0, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.90/2.09  thf('17', plain,
% 1.90/2.09      (![X2 : $i, X4 : $i]:
% 1.90/2.09         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.90/2.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.90/2.09  thf('18', plain,
% 1.90/2.09      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.90/2.09        | ((sk_B) = (k2_relat_1 @ sk_C)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['16', '17'])).
% 1.90/2.09  thf(t21_relat_1, axiom,
% 1.90/2.09    (![A:$i]:
% 1.90/2.09     ( ( v1_relat_1 @ A ) =>
% 1.90/2.09       ( r1_tarski @
% 1.90/2.09         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.90/2.09  thf('19', plain,
% 1.90/2.09      (![X19 : $i]:
% 1.90/2.09         ((r1_tarski @ X19 @ 
% 1.90/2.09           (k2_zfmisc_1 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19)))
% 1.90/2.09          | ~ (v1_relat_1 @ X19))),
% 1.90/2.09      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.90/2.09  thf(t12_xboole_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.90/2.09  thf('20', plain,
% 1.90/2.09      (![X8 : $i, X9 : $i]:
% 1.90/2.09         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 1.90/2.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.90/2.09  thf('21', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (~ (v1_relat_1 @ X0)
% 1.90/2.09          | ((k2_xboole_0 @ X0 @ 
% 1.90/2.09              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.90/2.09              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['19', '20'])).
% 1.90/2.09  thf(commutativity_k2_xboole_0, axiom,
% 1.90/2.09    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.90/2.09  thf('22', plain,
% 1.90/2.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.90/2.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.90/2.09  thf('23', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(t10_xboole_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.90/2.09  thf('24', plain,
% 1.90/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.90/2.09         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.90/2.09  thf('25', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ (k6_relat_1 @ sk_B) @ (k2_xboole_0 @ X0 @ sk_C))),
% 1.90/2.09      inference('sup-', [status(thm)], ['23', '24'])).
% 1.90/2.09  thf('26', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (r1_tarski @ (k6_relat_1 @ sk_B) @ (k2_xboole_0 @ sk_C @ X0))),
% 1.90/2.09      inference('sup+', [status(thm)], ['22', '25'])).
% 1.90/2.09  thf(t3_subset, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.90/2.09  thf('27', plain,
% 1.90/2.09      (![X10 : $i, X12 : $i]:
% 1.90/2.09         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.90/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.90/2.09  thf('28', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 1.90/2.09          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['26', '27'])).
% 1.90/2.09  thf('29', plain,
% 1.90/2.09      (((m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 1.90/2.09         (k1_zfmisc_1 @ 
% 1.90/2.09          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 1.90/2.09        | ~ (v1_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup+', [status(thm)], ['21', '28'])).
% 1.90/2.09  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 1.90/2.09      inference('demod', [status(thm)], ['13', '14'])).
% 1.90/2.09  thf('31', plain,
% 1.90/2.09      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 1.90/2.09        (k1_zfmisc_1 @ 
% 1.90/2.09         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.90/2.09      inference('demod', [status(thm)], ['29', '30'])).
% 1.90/2.09  thf('32', plain,
% 1.90/2.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.90/2.09         ((v5_relat_1 @ X22 @ X24)
% 1.90/2.09          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.90/2.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.90/2.09  thf('33', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup-', [status(thm)], ['31', '32'])).
% 1.90/2.09  thf('34', plain,
% 1.90/2.09      (![X15 : $i, X16 : $i]:
% 1.90/2.09         (~ (v5_relat_1 @ X15 @ X16)
% 1.90/2.09          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 1.90/2.09          | ~ (v1_relat_1 @ X15))),
% 1.90/2.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.90/2.09  thf('35', plain,
% 1.90/2.09      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 1.90/2.09        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_B)) @ (k2_relat_1 @ sk_C)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['33', '34'])).
% 1.90/2.09  thf('36', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf('37', plain,
% 1.90/2.09      (![X10 : $i, X12 : $i]:
% 1.90/2.09         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.90/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.90/2.09  thf('38', plain,
% 1.90/2.09      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ (k1_zfmisc_1 @ sk_C))),
% 1.90/2.09      inference('sup-', [status(thm)], ['36', '37'])).
% 1.90/2.09  thf('39', plain,
% 1.90/2.09      (![X13 : $i, X14 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.90/2.09          | (v1_relat_1 @ X13)
% 1.90/2.09          | ~ (v1_relat_1 @ X14))),
% 1.90/2.09      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.90/2.09  thf('40', plain,
% 1.90/2.09      ((~ (v1_relat_1 @ sk_C) | (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['38', '39'])).
% 1.90/2.09  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 1.90/2.09      inference('demod', [status(thm)], ['13', '14'])).
% 1.90/2.09  thf('42', plain, ((v1_relat_1 @ (k6_relat_1 @ sk_B))),
% 1.90/2.09      inference('demod', [status(thm)], ['40', '41'])).
% 1.90/2.09  thf(t71_relat_1, axiom,
% 1.90/2.09    (![A:$i]:
% 1.90/2.09     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.90/2.09       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.90/2.09  thf('43', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 1.90/2.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.90/2.09  thf('44', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))),
% 1.90/2.09      inference('demod', [status(thm)], ['35', '42', '43'])).
% 1.90/2.09  thf('45', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.90/2.09      inference('demod', [status(thm)], ['18', '44'])).
% 1.90/2.09  thf('46', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(redefinition_k2_relset_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.90/2.09       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.90/2.09  thf('47', plain,
% 1.90/2.09      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.90/2.09         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 1.90/2.09          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.90/2.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.90/2.09  thf('48', plain,
% 1.90/2.09      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup-', [status(thm)], ['46', '47'])).
% 1.90/2.09  thf('49', plain,
% 1.90/2.09      ((((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 1.90/2.09         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.90/2.09      inference('split', [status(esa)], ['0'])).
% 1.90/2.09  thf('50', plain,
% 1.90/2.09      ((((sk_B) != (k2_relat_1 @ sk_C)))
% 1.90/2.09         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['48', '49'])).
% 1.90/2.09  thf('51', plain,
% 1.90/2.09      ((((sk_B) != (sk_B)))
% 1.90/2.09         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['45', '50'])).
% 1.90/2.09  thf('52', plain, ((((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.09      inference('simplify', [status(thm)], ['51'])).
% 1.90/2.09  thf('53', plain,
% 1.90/2.09      (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.90/2.09       ~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.09      inference('split', [status(esa)], ['0'])).
% 1.90/2.09  thf('54', plain,
% 1.90/2.09      (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.90/2.09      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 1.90/2.09  thf('55', plain, (~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.90/2.09      inference('simpl_trail', [status(thm)], ['5', '54'])).
% 1.90/2.09  thf('56', plain,
% 1.90/2.09      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 1.90/2.09        (k1_zfmisc_1 @ 
% 1.90/2.09         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.90/2.09      inference('demod', [status(thm)], ['29', '30'])).
% 1.90/2.09  thf('57', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.90/2.09      inference('demod', [status(thm)], ['18', '44'])).
% 1.90/2.09  thf('58', plain,
% 1.90/2.09      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 1.90/2.09      inference('demod', [status(thm)], ['56', '57'])).
% 1.90/2.09  thf(dt_k1_relset_1, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.90/2.09       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.90/2.09  thf('59', plain,
% 1.90/2.09      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.90/2.09         ((m1_subset_1 @ (k1_relset_1 @ X25 @ X26 @ X27) @ (k1_zfmisc_1 @ X25))
% 1.90/2.09          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.90/2.09      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 1.90/2.09  thf('60', plain,
% 1.90/2.09      ((m1_subset_1 @ 
% 1.90/2.09        (k1_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ (k6_relat_1 @ sk_B)) @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k1_relat_1 @ sk_C)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['58', '59'])).
% 1.90/2.09  thf('61', plain,
% 1.90/2.09      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 1.90/2.09        (k1_zfmisc_1 @ 
% 1.90/2.09         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.90/2.09      inference('demod', [status(thm)], ['29', '30'])).
% 1.90/2.09  thf('62', plain,
% 1.90/2.09      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.90/2.09         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.90/2.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.90/2.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.90/2.09  thf('63', plain,
% 1.90/2.09      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.90/2.09         (k6_relat_1 @ sk_B)) = (k1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['61', '62'])).
% 1.90/2.09  thf('64', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 1.90/2.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.90/2.09  thf('65', plain,
% 1.90/2.09      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.90/2.09         (k6_relat_1 @ sk_B)) = (sk_B))),
% 1.90/2.09      inference('demod', [status(thm)], ['63', '64'])).
% 1.90/2.09  thf('66', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.90/2.09      inference('demod', [status(thm)], ['18', '44'])).
% 1.90/2.09  thf('67', plain,
% 1.90/2.09      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ sk_B @ (k6_relat_1 @ sk_B))
% 1.90/2.09         = (sk_B))),
% 1.90/2.09      inference('demod', [status(thm)], ['65', '66'])).
% 1.90/2.09  thf('68', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_C)))),
% 1.90/2.09      inference('demod', [status(thm)], ['60', '67'])).
% 1.90/2.09  thf('69', plain,
% 1.90/2.09      (![X10 : $i, X11 : $i]:
% 1.90/2.09         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.90/2.09  thf('70', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.90/2.09      inference('sup-', [status(thm)], ['68', '69'])).
% 1.90/2.09  thf('71', plain, ($false), inference('demod', [status(thm)], ['55', '70'])).
% 1.90/2.09  
% 1.90/2.09  % SZS output end Refutation
% 1.90/2.09  
% 1.90/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
