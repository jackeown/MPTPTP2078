%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YKJaxuTybA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:43 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 133 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  790 (1269 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_finset_1 @ X22 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( v1_finset_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_finset_1 @ X0 )
      | ( v1_finset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t33_finset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( v1_finset_1 @ A )
          & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ! [D: $i] :
              ~ ( ( v1_finset_1 @ D )
                & ( r1_tarski @ D @ B )
                & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_finset_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_finset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( v1_finset_1 @ E )
              & ( r1_tarski @ E @ C )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_finset_1 @ X24 )
      | ( r1_tarski @ ( sk_D @ X25 @ X26 @ X24 ) @ X26 )
      | ~ ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('5',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ X0 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) @ X16 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X21 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) @ X16 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X21 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) @ X1 ) )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X3 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X3 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) @ X1 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      = ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X27: $i] :
      ( ~ ( v1_finset_1 @ X27 )
      | ~ ( r1_tarski @ X27 @ sk_B )
      | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X27 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X0 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) @ sk_B )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_finset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','37'])).

thf('39',plain,
    ( ~ ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_finset_1 @ X24 )
      | ( v1_finset_1 @ ( sk_D @ X25 @ X26 @ X24 ) )
      | ~ ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('42',plain,
    ( ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_finset_1 @ X24 )
      | ( r1_tarski @ ( sk_E @ X25 @ X26 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('48',plain,
    ( ( r1_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) @ X16 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X21 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_finset_1 @ X24 )
      | ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ ( sk_D @ X25 @ X26 @ X24 ) @ ( sk_E @ X25 @ X26 @ X24 ) ) )
      | ~ ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('65',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['45','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YKJaxuTybA
% 0.14/0.37  % Computer   : n011.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:10:12 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.61/1.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.61/1.80  % Solved by: fo/fo7.sh
% 1.61/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.80  % done 2444 iterations in 1.314s
% 1.61/1.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.61/1.80  % SZS output start Refutation
% 1.61/1.80  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.61/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.61/1.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.61/1.80  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 1.61/1.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.61/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.61/1.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.61/1.80  thf(sk_C_type, type, sk_C: $i).
% 1.61/1.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.61/1.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.61/1.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.61/1.80  thf(t193_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 1.61/1.80  thf('0', plain,
% 1.61/1.80      (![X13 : $i, X14 : $i]:
% 1.61/1.80         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X13)),
% 1.61/1.80      inference('cnf', [status(esa)], [t193_relat_1])).
% 1.61/1.80  thf(t13_finset_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 1.61/1.80  thf('1', plain,
% 1.61/1.80      (![X22 : $i, X23 : $i]:
% 1.61/1.80         ((v1_finset_1 @ X22)
% 1.61/1.80          | ~ (r1_tarski @ X22 @ X23)
% 1.61/1.80          | ~ (v1_finset_1 @ X23))),
% 1.61/1.80      inference('cnf', [status(esa)], [t13_finset_1])).
% 1.61/1.80  thf('2', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (~ (v1_finset_1 @ X0)
% 1.61/1.80          | (v1_finset_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['0', '1'])).
% 1.61/1.80  thf(t33_finset_1, conjecture,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.61/1.80          ( ![D:$i]:
% 1.61/1.80            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 1.61/1.80                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ))).
% 1.61/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.80    (~( ![A:$i,B:$i,C:$i]:
% 1.61/1.80        ( ~( ( v1_finset_1 @ A ) & 
% 1.61/1.80             ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.61/1.80             ( ![D:$i]:
% 1.61/1.80               ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 1.61/1.80                    ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ) )),
% 1.61/1.80    inference('cnf.neg', [status(esa)], [t33_finset_1])).
% 1.61/1.80  thf('3', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf(t32_finset_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.61/1.80          ( ![D:$i,E:$i]:
% 1.61/1.80            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 1.61/1.80                 ( v1_finset_1 @ E ) & ( r1_tarski @ E @ C ) & 
% 1.61/1.80                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) ) ) ))).
% 1.61/1.80  thf('4', plain,
% 1.61/1.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.61/1.80         (~ (v1_finset_1 @ X24)
% 1.61/1.80          | (r1_tarski @ (sk_D @ X25 @ X26 @ X24) @ X26)
% 1.61/1.80          | ~ (r1_tarski @ X24 @ (k2_zfmisc_1 @ X26 @ X25)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t32_finset_1])).
% 1.61/1.80  thf('5', plain,
% 1.61/1.80      (((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 1.61/1.80        | ~ (v1_finset_1 @ sk_A))),
% 1.61/1.80      inference('sup-', [status(thm)], ['3', '4'])).
% 1.61/1.80  thf('6', plain, ((v1_finset_1 @ sk_A)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('7', plain, ((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 1.61/1.80      inference('demod', [status(thm)], ['5', '6'])).
% 1.61/1.80  thf('8', plain,
% 1.61/1.80      (![X13 : $i, X14 : $i]:
% 1.61/1.80         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X13)),
% 1.61/1.80      inference('cnf', [status(esa)], [t193_relat_1])).
% 1.61/1.80  thf(t1_xboole_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.61/1.80       ( r1_tarski @ A @ C ) ))).
% 1.61/1.80  thf('9', plain,
% 1.61/1.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.61/1.80         (~ (r1_tarski @ X3 @ X4)
% 1.61/1.80          | ~ (r1_tarski @ X4 @ X5)
% 1.61/1.80          | (r1_tarski @ X3 @ X5))),
% 1.61/1.80      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.61/1.80  thf('10', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2)
% 1.61/1.80          | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.80      inference('sup-', [status(thm)], ['8', '9'])).
% 1.61/1.80  thf('11', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (r1_tarski @ 
% 1.61/1.80          (k1_relat_1 @ (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ X0)) @ 
% 1.61/1.80          sk_B)),
% 1.61/1.80      inference('sup-', [status(thm)], ['7', '10'])).
% 1.61/1.80  thf(t194_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 1.61/1.80  thf('12', plain,
% 1.61/1.80      (![X15 : $i, X16 : $i]:
% 1.61/1.80         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) @ X16)),
% 1.61/1.80      inference('cnf', [status(esa)], [t194_relat_1])).
% 1.61/1.80  thf(d10_xboole_0, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.61/1.80  thf('13', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.61/1.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.80  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.61/1.80      inference('simplify', [status(thm)], ['13'])).
% 1.61/1.80  thf(t11_relset_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ C ) =>
% 1.61/1.80       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.61/1.80           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.61/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.61/1.80  thf('15', plain,
% 1.61/1.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.80         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ X21)
% 1.61/1.80          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.61/1.80          | ~ (v1_relat_1 @ X19))),
% 1.61/1.80      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.61/1.80  thf('16', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X0)
% 1.61/1.80          | (m1_subset_1 @ X0 @ 
% 1.61/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.61/1.80      inference('sup-', [status(thm)], ['14', '15'])).
% 1.61/1.80  thf('17', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 1.61/1.80           (k1_zfmisc_1 @ 
% 1.61/1.80            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))
% 1.61/1.80          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['12', '16'])).
% 1.61/1.80  thf(fc6_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.61/1.80  thf('18', plain,
% 1.61/1.80      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 1.61/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.61/1.80  thf('19', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 1.61/1.80          (k1_zfmisc_1 @ 
% 1.61/1.80           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['17', '18'])).
% 1.61/1.80  thf(t3_subset, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.61/1.80  thf('20', plain,
% 1.61/1.80      (![X6 : $i, X7 : $i]:
% 1.61/1.80         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t3_subset])).
% 1.61/1.80  thf('21', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 1.61/1.80          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['19', '20'])).
% 1.61/1.80  thf('22', plain,
% 1.61/1.80      (![X0 : $i, X2 : $i]:
% 1.61/1.80         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.80  thf('23', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (~ (r1_tarski @ 
% 1.61/1.80             (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0) @ 
% 1.61/1.80             (k2_zfmisc_1 @ X1 @ X0))
% 1.61/1.80          | ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 1.61/1.80              = (k2_zfmisc_1 @ X1 @ X0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['21', '22'])).
% 1.61/1.80  thf('24', plain,
% 1.61/1.80      (![X15 : $i, X16 : $i]:
% 1.61/1.80         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) @ X16)),
% 1.61/1.80      inference('cnf', [status(esa)], [t194_relat_1])).
% 1.61/1.80  thf('25', plain,
% 1.61/1.80      (![X13 : $i, X14 : $i]:
% 1.61/1.80         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X13)),
% 1.61/1.80      inference('cnf', [status(esa)], [t193_relat_1])).
% 1.61/1.80  thf('26', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2)
% 1.61/1.80          | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.80      inference('sup-', [status(thm)], ['8', '9'])).
% 1.61/1.80  thf('27', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         (r1_tarski @ 
% 1.61/1.80          (k1_relat_1 @ 
% 1.61/1.80           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2)) @ 
% 1.61/1.80          X0)),
% 1.61/1.80      inference('sup-', [status(thm)], ['25', '26'])).
% 1.61/1.80  thf('28', plain,
% 1.61/1.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.80         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ X21)
% 1.61/1.80          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.61/1.80          | ~ (v1_relat_1 @ X19))),
% 1.61/1.80      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.61/1.80  thf('29', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ 
% 1.61/1.80             (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X2)) @ X1))
% 1.61/1.80          | (m1_subset_1 @ 
% 1.61/1.80             (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X2)) @ X1) @ 
% 1.61/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X3)))
% 1.61/1.80          | ~ (r1_tarski @ 
% 1.61/1.80               (k2_relat_1 @ 
% 1.61/1.80                (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X2)) @ X1)) @ 
% 1.61/1.80               X3))),
% 1.61/1.80      inference('sup-', [status(thm)], ['27', '28'])).
% 1.61/1.80  thf('30', plain,
% 1.61/1.80      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 1.61/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.61/1.80  thf('31', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.61/1.80         ((m1_subset_1 @ 
% 1.61/1.80           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X2)) @ X1) @ 
% 1.61/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X3)))
% 1.61/1.80          | ~ (r1_tarski @ 
% 1.61/1.80               (k2_relat_1 @ 
% 1.61/1.80                (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X2)) @ X1)) @ 
% 1.61/1.80               X3))),
% 1.61/1.80      inference('demod', [status(thm)], ['29', '30'])).
% 1.61/1.80  thf('32', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         (m1_subset_1 @ 
% 1.61/1.80          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X2 @ X1)) @ X0) @ 
% 1.61/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['24', '31'])).
% 1.61/1.80  thf('33', plain,
% 1.61/1.80      (![X6 : $i, X7 : $i]:
% 1.61/1.80         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t3_subset])).
% 1.61/1.80  thf('34', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         (r1_tarski @ 
% 1.61/1.80          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X2)) @ X0) @ 
% 1.61/1.80          (k2_zfmisc_1 @ X1 @ X0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['32', '33'])).
% 1.61/1.80  thf('35', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 1.61/1.80           = (k2_zfmisc_1 @ X1 @ X0))),
% 1.61/1.80      inference('demod', [status(thm)], ['23', '34'])).
% 1.61/1.80  thf('36', plain,
% 1.61/1.80      (![X27 : $i]:
% 1.61/1.80         (~ (v1_finset_1 @ X27)
% 1.61/1.80          | ~ (r1_tarski @ X27 @ sk_B)
% 1.61/1.80          | ~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X27 @ sk_C)))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('37', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X0 @ sk_C))
% 1.61/1.80          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_C)) @ sk_B)
% 1.61/1.80          | ~ (v1_finset_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['35', '36'])).
% 1.61/1.80  thf('38', plain,
% 1.61/1.80      ((~ (v1_finset_1 @ 
% 1.61/1.80           (k1_relat_1 @ (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)))
% 1.61/1.80        | ~ (r1_tarski @ sk_A @ 
% 1.61/1.80             (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['11', '37'])).
% 1.61/1.80  thf('39', plain,
% 1.61/1.80      ((~ (v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 1.61/1.80        | ~ (r1_tarski @ sk_A @ 
% 1.61/1.80             (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['2', '38'])).
% 1.61/1.80  thf('40', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('41', plain,
% 1.61/1.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.61/1.80         (~ (v1_finset_1 @ X24)
% 1.61/1.80          | (v1_finset_1 @ (sk_D @ X25 @ X26 @ X24))
% 1.61/1.80          | ~ (r1_tarski @ X24 @ (k2_zfmisc_1 @ X26 @ X25)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t32_finset_1])).
% 1.61/1.80  thf('42', plain,
% 1.61/1.80      (((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)) | ~ (v1_finset_1 @ sk_A))),
% 1.61/1.80      inference('sup-', [status(thm)], ['40', '41'])).
% 1.61/1.80  thf('43', plain, ((v1_finset_1 @ sk_A)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('44', plain, ((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 1.61/1.80      inference('demod', [status(thm)], ['42', '43'])).
% 1.61/1.80  thf('45', plain,
% 1.61/1.80      (~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 1.61/1.80      inference('demod', [status(thm)], ['39', '44'])).
% 1.61/1.80  thf('46', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('47', plain,
% 1.61/1.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.61/1.80         (~ (v1_finset_1 @ X24)
% 1.61/1.80          | (r1_tarski @ (sk_E @ X25 @ X26 @ X24) @ X25)
% 1.61/1.80          | ~ (r1_tarski @ X24 @ (k2_zfmisc_1 @ X26 @ X25)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t32_finset_1])).
% 1.61/1.80  thf('48', plain,
% 1.61/1.80      (((r1_tarski @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)
% 1.61/1.80        | ~ (v1_finset_1 @ sk_A))),
% 1.61/1.80      inference('sup-', [status(thm)], ['46', '47'])).
% 1.61/1.80  thf('49', plain, ((v1_finset_1 @ sk_A)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('50', plain, ((r1_tarski @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 1.61/1.80      inference('demod', [status(thm)], ['48', '49'])).
% 1.61/1.80  thf('51', plain,
% 1.61/1.80      (![X15 : $i, X16 : $i]:
% 1.61/1.80         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) @ X16)),
% 1.61/1.80      inference('cnf', [status(esa)], [t194_relat_1])).
% 1.61/1.80  thf('52', plain,
% 1.61/1.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.61/1.80         (~ (r1_tarski @ X3 @ X4)
% 1.61/1.80          | ~ (r1_tarski @ X4 @ X5)
% 1.61/1.80          | (r1_tarski @ X3 @ X5))),
% 1.61/1.80      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.61/1.80  thf('53', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         ((r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 1.61/1.80          | ~ (r1_tarski @ X0 @ X2))),
% 1.61/1.80      inference('sup-', [status(thm)], ['51', '52'])).
% 1.61/1.80  thf('54', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (r1_tarski @ 
% 1.61/1.80          (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 1.61/1.80          sk_C)),
% 1.61/1.80      inference('sup-', [status(thm)], ['50', '53'])).
% 1.61/1.80  thf('55', plain,
% 1.61/1.80      (![X13 : $i, X14 : $i]:
% 1.61/1.80         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X13)),
% 1.61/1.80      inference('cnf', [status(esa)], [t193_relat_1])).
% 1.61/1.80  thf('56', plain,
% 1.61/1.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.80         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ X21)
% 1.61/1.80          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.61/1.80          | ~ (v1_relat_1 @ X19))),
% 1.61/1.80      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.61/1.80  thf('57', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 1.61/1.80          | (m1_subset_1 @ (k2_zfmisc_1 @ X0 @ X1) @ 
% 1.61/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2))),
% 1.61/1.80      inference('sup-', [status(thm)], ['55', '56'])).
% 1.61/1.80  thf('58', plain,
% 1.61/1.80      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 1.61/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.61/1.80  thf('59', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.80         ((m1_subset_1 @ (k2_zfmisc_1 @ X0 @ X1) @ 
% 1.61/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 1.61/1.80          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X2))),
% 1.61/1.80      inference('demod', [status(thm)], ['57', '58'])).
% 1.61/1.80  thf('60', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (m1_subset_1 @ (k2_zfmisc_1 @ X0 @ (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 1.61/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['54', '59'])).
% 1.61/1.80  thf('61', plain,
% 1.61/1.80      (![X6 : $i, X7 : $i]:
% 1.61/1.80         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t3_subset])).
% 1.61/1.80  thf('62', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 1.61/1.80          (k2_zfmisc_1 @ X0 @ sk_C))),
% 1.61/1.80      inference('sup-', [status(thm)], ['60', '61'])).
% 1.61/1.80  thf('63', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('64', plain,
% 1.61/1.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.61/1.80         (~ (v1_finset_1 @ X24)
% 1.61/1.80          | (r1_tarski @ X24 @ 
% 1.61/1.80             (k2_zfmisc_1 @ (sk_D @ X25 @ X26 @ X24) @ (sk_E @ X25 @ X26 @ X24)))
% 1.61/1.80          | ~ (r1_tarski @ X24 @ (k2_zfmisc_1 @ X26 @ X25)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t32_finset_1])).
% 1.61/1.80  thf('65', plain,
% 1.61/1.80      (((r1_tarski @ sk_A @ 
% 1.61/1.80         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 1.61/1.80          (sk_E @ sk_C @ sk_B @ sk_A)))
% 1.61/1.80        | ~ (v1_finset_1 @ sk_A))),
% 1.61/1.80      inference('sup-', [status(thm)], ['63', '64'])).
% 1.61/1.80  thf('66', plain, ((v1_finset_1 @ sk_A)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('67', plain,
% 1.61/1.80      ((r1_tarski @ sk_A @ 
% 1.61/1.80        (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 1.61/1.80         (sk_E @ sk_C @ sk_B @ sk_A)))),
% 1.61/1.80      inference('demod', [status(thm)], ['65', '66'])).
% 1.61/1.80  thf('68', plain,
% 1.61/1.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.61/1.80         (~ (r1_tarski @ X3 @ X4)
% 1.61/1.80          | ~ (r1_tarski @ X4 @ X5)
% 1.61/1.80          | (r1_tarski @ X3 @ X5))),
% 1.61/1.80      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.61/1.80  thf('69', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         ((r1_tarski @ sk_A @ X0)
% 1.61/1.80          | ~ (r1_tarski @ 
% 1.61/1.80               (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 1.61/1.80                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 1.61/1.80               X0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['67', '68'])).
% 1.61/1.80  thf('70', plain,
% 1.61/1.80      ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 1.61/1.80      inference('sup-', [status(thm)], ['62', '69'])).
% 1.61/1.80  thf('71', plain, ($false), inference('demod', [status(thm)], ['45', '70'])).
% 1.61/1.80  
% 1.61/1.80  % SZS output end Refutation
% 1.61/1.80  
% 1.61/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
