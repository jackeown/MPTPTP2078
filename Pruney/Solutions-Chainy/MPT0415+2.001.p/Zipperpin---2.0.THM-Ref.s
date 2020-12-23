%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kGbm7S2hbU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:09 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 239 expanded)
%              Number of leaves         :   29 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  941 (2247 expanded)
%              Number of equality atoms :   64 ( 212 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X19 @ X18 ) @ X17 )
      | ( r2_hidden @ ( k3_subset_1 @ X18 @ ( sk_D @ X17 @ X19 @ X18 ) ) @ X19 )
      | ( X17
        = ( k7_setfam_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X17 @ X19 @ X18 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ( X17
        = ( k7_setfam_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k6_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    = ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','21'])).

thf('23',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_A )
    = ( sk_D @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    = ( sk_D @ sk_B @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','32'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k6_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ ( k6_subset_1 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','40'])).

thf('42',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( X17
       != ( k7_setfam_1 @ X18 @ X19 ) )
      | ( r2_hidden @ X20 @ X17 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X18 @ X20 ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X18 @ X20 ) @ X19 )
      | ( r2_hidden @ X20 @ ( k7_setfam_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('48',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','50','51','52'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','58'])).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','61'])).

thf('63',plain,(
    r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['22','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ ( k6_subset_1 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k6_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ ( k6_subset_1 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ ( k6_subset_1 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('73',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','57'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('sup-',[status(thm)],['63','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kGbm7S2hbU
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.97  % Solved by: fo/fo7.sh
% 0.75/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.97  % done 841 iterations in 0.494s
% 0.75/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.97  % SZS output start Refutation
% 0.75/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.75/0.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.97  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.75/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.97  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.75/0.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.75/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.97  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.75/0.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.97  thf(t46_setfam_1, conjecture,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.97       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.75/0.97            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.75/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.97    (~( ![A:$i,B:$i]:
% 0.75/0.97        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.97          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.75/0.97               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.75/0.97    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.75/0.97  thf('0', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('1', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(d8_setfam_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.97       ( ![C:$i]:
% 0.75/0.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.97           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.75/0.97             ( ![D:$i]:
% 0.75/0.97               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.97                 ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.97                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.75/0.97  thf('2', plain,
% 0.75/0.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.75/0.97          | (r2_hidden @ (sk_D @ X17 @ X19 @ X18) @ X17)
% 0.75/0.97          | (r2_hidden @ (k3_subset_1 @ X18 @ (sk_D @ X17 @ X19 @ X18)) @ X19)
% 0.75/0.97          | ((X17) = (k7_setfam_1 @ X18 @ X19))
% 0.75/0.97          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.75/0.97      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.75/0.97  thf('3', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.75/0.97          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.75/0.97          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A)) @ X0)
% 0.75/0.97          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.75/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.97  thf('4', plain,
% 0.75/0.97      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.75/0.97        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.75/0.97           sk_B)
% 0.75/0.97        | ((sk_B) = (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['0', '3'])).
% 0.75/0.97  thf('5', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('6', plain,
% 0.75/0.97      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.75/0.97        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.75/0.97           sk_B)
% 0.75/0.97        | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.97  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('8', plain,
% 0.75/0.97      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.75/0.97        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.75/0.97           sk_B))),
% 0.75/0.97      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.75/0.97  thf('9', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('10', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('11', plain,
% 0.75/0.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.75/0.97          | (m1_subset_1 @ (sk_D @ X17 @ X19 @ X18) @ (k1_zfmisc_1 @ X18))
% 0.75/0.97          | ((X17) = (k7_setfam_1 @ X18 @ X19))
% 0.75/0.97          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.75/0.97      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.75/0.97  thf('12', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.75/0.97          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.75/0.97          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.97  thf('13', plain,
% 0.75/0.97      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.97        | ((sk_B) = (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['9', '12'])).
% 0.75/0.97  thf('14', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('15', plain,
% 0.75/0.97      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.97        | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['13', '14'])).
% 0.75/0.97  thf('16', plain, (((sk_B) != (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('17', plain,
% 0.75/0.97      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.97      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.75/0.97  thf(d5_subset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.75/0.97  thf('18', plain,
% 0.75/0.97      (![X11 : $i, X12 : $i]:
% 0.75/0.97         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.75/0.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.75/0.97  thf(redefinition_k6_subset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.75/0.97  thf('19', plain,
% 0.75/0.97      (![X15 : $i, X16 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.75/0.97      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.75/0.97  thf('20', plain,
% 0.75/0.97      (![X11 : $i, X12 : $i]:
% 0.75/0.97         (((k3_subset_1 @ X11 @ X12) = (k6_subset_1 @ X11 @ X12))
% 0.75/0.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.75/0.97      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.97  thf('21', plain,
% 0.75/0.97      (((k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.75/0.97         = (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['17', '20'])).
% 0.75/0.97  thf('22', plain,
% 0.75/0.97      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.75/0.97        | (r2_hidden @ (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.75/0.97           sk_B))),
% 0.75/0.97      inference('demod', [status(thm)], ['8', '21'])).
% 0.75/0.97  thf('23', plain,
% 0.75/0.97      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.97      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.75/0.97  thf(t3_subset, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.97  thf('24', plain,
% 0.75/0.97      (![X25 : $i, X26 : $i]:
% 0.75/0.97         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.97  thf('25', plain, ((r1_tarski @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.75/0.97      inference('sup-', [status(thm)], ['23', '24'])).
% 0.75/0.97  thf(t28_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.97  thf('26', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('27', plain,
% 0.75/0.97      (((k3_xboole_0 @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_A)
% 0.75/0.97         = (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.75/0.97      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.97  thf(commutativity_k2_tarski, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.75/0.97  thf('28', plain,
% 0.75/0.97      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.75/0.97  thf(t12_setfam_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.97  thf('29', plain,
% 0.75/0.97      (![X23 : $i, X24 : $i]:
% 0.75/0.97         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 0.75/0.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.97  thf('30', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['28', '29'])).
% 0.75/0.97  thf('31', plain,
% 0.75/0.97      (![X23 : $i, X24 : $i]:
% 0.75/0.97         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 0.75/0.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.75/0.97  thf('32', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.97  thf('33', plain,
% 0.75/0.97      (((k3_xboole_0 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.75/0.97         = (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.75/0.97      inference('demod', [status(thm)], ['27', '32'])).
% 0.75/0.97  thf(dt_k6_subset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.75/0.97  thf('34', plain,
% 0.75/0.97      (![X13 : $i, X14 : $i]:
% 0.75/0.97         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.75/0.97  thf('35', plain,
% 0.75/0.97      (![X11 : $i, X12 : $i]:
% 0.75/0.97         (((k3_subset_1 @ X11 @ X12) = (k6_subset_1 @ X11 @ X12))
% 0.75/0.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.75/0.97      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.97  thf('36', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.75/0.97           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['34', '35'])).
% 0.75/0.97  thf(t48_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.97  thf('37', plain,
% 0.75/0.97      (![X2 : $i, X3 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.75/0.97           = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.97  thf('38', plain,
% 0.75/0.97      (![X15 : $i, X16 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.75/0.97      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.75/0.97  thf('39', plain,
% 0.75/0.97      (![X15 : $i, X16 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.75/0.97      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.75/0.97  thf('40', plain,
% 0.75/0.97      (![X2 : $i, X3 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X2 @ (k6_subset_1 @ X2 @ X3))
% 0.75/0.97           = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.97      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.75/0.97  thf('41', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.75/0.97           = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('demod', [status(thm)], ['36', '40'])).
% 0.75/0.97  thf('42', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('43', plain,
% 0.75/0.97      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.75/0.97          | ((X17) != (k7_setfam_1 @ X18 @ X19))
% 0.75/0.97          | (r2_hidden @ X20 @ X17)
% 0.75/0.97          | ~ (r2_hidden @ (k3_subset_1 @ X18 @ X20) @ X19)
% 0.75/0.97          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X18))
% 0.75/0.97          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.75/0.97      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.75/0.97  thf('44', plain,
% 0.75/0.97      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.75/0.97          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X18))
% 0.75/0.97          | ~ (r2_hidden @ (k3_subset_1 @ X18 @ X20) @ X19)
% 0.75/0.97          | (r2_hidden @ X20 @ (k7_setfam_1 @ X18 @ X19))
% 0.75/0.97          | ~ (m1_subset_1 @ (k7_setfam_1 @ X18 @ X19) @ 
% 0.75/0.97               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.75/0.97      inference('simplify', [status(thm)], ['43'])).
% 0.75/0.97  thf('45', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.75/0.97          | (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.75/0.97          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.75/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.97          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['42', '44'])).
% 0.75/0.97  thf('46', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(dt_k7_setfam_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.97       ( m1_subset_1 @
% 0.75/0.97         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.75/0.97  thf('47', plain,
% 0.75/0.97      (![X21 : $i, X22 : $i]:
% 0.75/0.97         ((m1_subset_1 @ (k7_setfam_1 @ X21 @ X22) @ 
% 0.75/0.97           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21)))
% 0.75/0.97          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.75/0.97  thf('48', plain,
% 0.75/0.97      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.75/0.97        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['46', '47'])).
% 0.75/0.97  thf('49', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('50', plain,
% 0.75/0.97      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('demod', [status(thm)], ['48', '49'])).
% 0.75/0.97  thf('51', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('52', plain,
% 0.75/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('53', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.75/0.97          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.75/0.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('demod', [status(thm)], ['45', '50', '51', '52'])).
% 0.75/0.97  thf(t113_zfmisc_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.75/0.97       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.75/0.97  thf('54', plain,
% 0.75/0.97      (![X7 : $i, X8 : $i]:
% 0.75/0.97         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.97  thf('55', plain,
% 0.75/0.97      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['54'])).
% 0.75/0.97  thf(t152_zfmisc_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.75/0.97  thf('56', plain,
% 0.75/0.97      (![X9 : $i, X10 : $i]: ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.75/0.97      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.75/0.97  thf('57', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.97      inference('sup-', [status(thm)], ['55', '56'])).
% 0.75/0.97  thf('58', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.97          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.75/0.97      inference('clc', [status(thm)], ['53', '57'])).
% 0.75/0.97  thf('59', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (r2_hidden @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.75/0.97          | ~ (m1_subset_1 @ (k6_subset_1 @ sk_A @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['41', '58'])).
% 0.75/0.97  thf('60', plain,
% 0.75/0.97      (![X13 : $i, X14 : $i]:
% 0.75/0.97         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.75/0.97  thf('61', plain,
% 0.75/0.97      (![X0 : $i]: ~ (r2_hidden @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.75/0.97      inference('demod', [status(thm)], ['59', '60'])).
% 0.75/0.97  thf('62', plain, (~ (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)),
% 0.75/0.97      inference('sup-', [status(thm)], ['33', '61'])).
% 0.75/0.97  thf('63', plain,
% 0.75/0.97      ((r2_hidden @ (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ sk_B)),
% 0.75/0.97      inference('clc', [status(thm)], ['22', '62'])).
% 0.75/0.97  thf('64', plain,
% 0.75/0.97      (![X2 : $i, X3 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X2 @ (k6_subset_1 @ X2 @ X3))
% 0.75/0.97           = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.97      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.75/0.97  thf('65', plain,
% 0.75/0.97      (![X13 : $i, X14 : $i]:
% 0.75/0.97         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.75/0.97  thf('66', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['64', '65'])).
% 0.75/0.97  thf('67', plain,
% 0.75/0.97      (![X11 : $i, X12 : $i]:
% 0.75/0.97         (((k3_subset_1 @ X11 @ X12) = (k6_subset_1 @ X11 @ X12))
% 0.75/0.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.75/0.97      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.97  thf('68', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.75/0.97           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['66', '67'])).
% 0.75/0.97  thf('69', plain,
% 0.75/0.97      (![X2 : $i, X3 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X2 @ (k6_subset_1 @ X2 @ X3))
% 0.75/0.97           = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.97      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.75/0.97  thf('70', plain,
% 0.75/0.97      (![X2 : $i, X3 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X2 @ (k6_subset_1 @ X2 @ X3))
% 0.75/0.97           = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.97      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.75/0.97  thf('71', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.97           = (k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['69', '70'])).
% 0.75/0.97  thf('72', plain,
% 0.75/0.97      (![X13 : $i, X14 : $i]:
% 0.75/0.97         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.75/0.97  thf('73', plain,
% 0.75/0.97      (![X25 : $i, X26 : $i]:
% 0.75/0.97         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.97  thf('74', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.75/0.97      inference('sup-', [status(thm)], ['72', '73'])).
% 0.75/0.97  thf('75', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('76', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0)
% 0.75/0.97           = (k6_subset_1 @ X0 @ X1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['74', '75'])).
% 0.75/0.97  thf('77', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.97  thf('78', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.75/0.97           = (k6_subset_1 @ X0 @ X1))),
% 0.75/0.97      inference('demod', [status(thm)], ['76', '77'])).
% 0.75/0.97  thf('79', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.97           = (k6_subset_1 @ X1 @ X0))),
% 0.75/0.97      inference('demod', [status(thm)], ['71', '78'])).
% 0.75/0.97  thf('80', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.75/0.97           = (k6_subset_1 @ X0 @ X1))),
% 0.75/0.97      inference('demod', [status(thm)], ['68', '79'])).
% 0.75/0.97  thf('81', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.97          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.75/0.97      inference('clc', [status(thm)], ['53', '57'])).
% 0.75/0.97  thf('82', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (r2_hidden @ (k6_subset_1 @ sk_A @ X0) @ sk_B)
% 0.75/0.97          | ~ (m1_subset_1 @ (k3_xboole_0 @ sk_A @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['80', '81'])).
% 0.75/0.97  thf('83', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['64', '65'])).
% 0.75/0.97  thf('84', plain,
% 0.75/0.97      (![X0 : $i]: ~ (r2_hidden @ (k6_subset_1 @ sk_A @ X0) @ sk_B)),
% 0.75/0.97      inference('demod', [status(thm)], ['82', '83'])).
% 0.75/0.97  thf('85', plain, ($false), inference('sup-', [status(thm)], ['63', '84'])).
% 0.75/0.97  
% 0.75/0.97  % SZS output end Refutation
% 0.75/0.97  
% 0.75/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
