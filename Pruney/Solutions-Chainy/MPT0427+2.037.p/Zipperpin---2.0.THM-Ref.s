%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SkNlw2MMxt

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:25 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 128 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  650 (1104 expanded)
%              Number of equality atoms :   56 (  67 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t59_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X33 @ X34 )
      | ( r1_tarski @ ( k1_setfam_1 @ X34 ) @ ( k1_setfam_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X22 @ X21 )
        = ( k6_setfam_1 @ X22 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('6',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k6_setfam_1 @ X26 @ X25 )
        = ( k1_setfam_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('9',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X22 @ X21 )
        = ( k6_setfam_1 @ X22 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('13',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_2 )
      = ( k6_setfam_1 @ sk_A @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k6_setfam_1 @ sk_A @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k6_setfam_1 @ X26 @ X25 )
        = ( k1_setfam_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('18',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_2 )
    = ( k1_setfam_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C_2 ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('24',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_C_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','55'])).

thf('57',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X22 @ X21 )
        = X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('59',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) )
      | ( ( k8_setfam_1 @ X22 @ k1_xboole_0 )
        = X22 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('61',plain,(
    ! [X22: $i] :
      ( ( k8_setfam_1 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('64',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57','61','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SkNlw2MMxt
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:06:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 253 iterations in 0.088s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.53  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.53  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.19/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(t59_setfam_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53       ( ![C:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53           ( ( r1_tarski @ B @ C ) =>
% 0.19/0.53             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i]:
% 0.19/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53          ( ![C:$i]:
% 0.19/0.53            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53              ( ( r1_tarski @ B @ C ) =>
% 0.19/0.53                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.19/0.53          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(t7_setfam_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.53         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X33 : $i, X34 : $i]:
% 0.19/0.53         (((X33) = (k1_xboole_0))
% 0.19/0.53          | ~ (r1_tarski @ X33 @ X34)
% 0.19/0.53          | (r1_tarski @ (k1_setfam_1 @ X34) @ (k1_setfam_1 @ X33)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (((r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B_1))
% 0.19/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d10_setfam_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.53           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.19/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X21 : $i, X22 : $i]:
% 0.19/0.53         (((X21) = (k1_xboole_0))
% 0.19/0.53          | ((k8_setfam_1 @ X22 @ X21) = (k6_setfam_1 @ X22 @ X21))
% 0.19/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.19/0.53      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.19/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(redefinition_k6_setfam_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X25 : $i, X26 : $i]:
% 0.19/0.53         (((k6_setfam_1 @ X26 @ X25) = (k1_setfam_1 @ X25))
% 0.19/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X26))))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.19/0.53  thf('9', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))
% 0.19/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X21 : $i, X22 : $i]:
% 0.19/0.53         (((X21) = (k1_xboole_0))
% 0.19/0.53          | ((k8_setfam_1 @ X22 @ X21) = (k6_setfam_1 @ X22 @ X21))
% 0.19/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.19/0.53      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      ((((k8_setfam_1 @ sk_A @ sk_C_2) = (k6_setfam_1 @ sk_A @ sk_C_2))
% 0.19/0.53        | ((sk_C_2) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.19/0.53          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      ((~ (r1_tarski @ (k6_setfam_1 @ sk_A @ sk_C_2) @ 
% 0.19/0.53           (k8_setfam_1 @ sk_A @ sk_B_1))
% 0.19/0.53        | ((sk_C_2) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X25 : $i, X26 : $i]:
% 0.19/0.53         (((k6_setfam_1 @ X26 @ X25) = (k1_setfam_1 @ X25))
% 0.19/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X26))))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.19/0.53  thf('18', plain, (((k6_setfam_1 @ sk_A @ sk_C_2) = (k1_setfam_1 @ sk_C_2))),
% 0.19/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k8_setfam_1 @ sk_A @ sk_B_1))
% 0.19/0.53        | ((sk_C_2) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C_2) @ (k1_setfam_1 @ sk_B_1))
% 0.19/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.53        | ((sk_C_2) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['10', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      ((((sk_B_1) = (k1_xboole_0))
% 0.19/0.53        | ((sk_C_2) = (k1_xboole_0))
% 0.19/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '20'])).
% 0.19/0.53  thf('22', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.53  thf(t7_xboole_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.53  thf('24', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d3_tarski, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.53          | (r2_hidden @ X0 @ X2)
% 0.19/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_C_2))),
% 0.19/0.53      inference('sup-', [status(thm)], ['23', '26'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X1 : $i, X3 : $i]:
% 0.19/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (![X1 : $i, X3 : $i]:
% 0.19/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.53  thf('31', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.53  thf(t28_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X9 : $i, X10 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.53  thf('33', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.53  thf(t4_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.19/0.53          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      ((((sk_B_1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ sk_C_2 @ sk_C_2))),
% 0.19/0.53      inference('sup-', [status(thm)], ['27', '35'])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      ((~ (r1_xboole_0 @ k1_xboole_0 @ sk_C_2)
% 0.19/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['22', '36'])).
% 0.19/0.53  thf(t4_subset_1, axiom,
% 0.19/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.53  thf(t3_subset, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (![X27 : $i, X28 : $i]:
% 0.19/0.53         ((r1_tarski @ X27 @ X28) | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.53  thf('40', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      (![X9 : $i, X10 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      (![X4 : $i, X5 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X4 @ X5)
% 0.19/0.53          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.53          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['42', '43'])).
% 0.19/0.53  thf(t46_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (![X11 : $i, X12 : $i]:
% 0.19/0.53         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 0.19/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.19/0.53  thf(t83_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (![X15 : $i, X17 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((k1_xboole_0) != (X0))
% 0.19/0.53          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.53  thf('48', plain,
% 0.19/0.53      (![X1 : $i]:
% 0.19/0.53         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['47'])).
% 0.19/0.53  thf(t7_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.53  thf('49', plain,
% 0.19/0.53      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.19/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.53  thf('50', plain,
% 0.19/0.53      (![X9 : $i, X10 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.53  thf('51', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.53  thf('52', plain,
% 0.19/0.53      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.19/0.53          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X2 @ X0)
% 0.19/0.53          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.53  thf('54', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['48', '53'])).
% 0.19/0.53  thf('55', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.19/0.53      inference('sup-', [status(thm)], ['44', '54'])).
% 0.19/0.53  thf('56', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.53      inference('demod', [status(thm)], ['37', '55'])).
% 0.19/0.53  thf('57', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      (![X21 : $i, X22 : $i]:
% 0.19/0.53         (((X21) != (k1_xboole_0))
% 0.19/0.53          | ((k8_setfam_1 @ X22 @ X21) = (X22))
% 0.19/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.19/0.53      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.19/0.53  thf('59', plain,
% 0.19/0.53      (![X22 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22)))
% 0.19/0.53          | ((k8_setfam_1 @ X22 @ k1_xboole_0) = (X22)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['58'])).
% 0.19/0.53  thf('60', plain,
% 0.19/0.53      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.53  thf('61', plain, (![X22 : $i]: ((k8_setfam_1 @ X22 @ k1_xboole_0) = (X22))),
% 0.19/0.53      inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.53  thf('62', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(dt_k8_setfam_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.53       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.53  thf('63', plain,
% 0.19/0.53      (![X23 : $i, X24 : $i]:
% 0.19/0.53         ((m1_subset_1 @ (k8_setfam_1 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 0.19/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23))))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.19/0.53  thf('64', plain,
% 0.19/0.53      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.19/0.53  thf('65', plain,
% 0.19/0.53      (![X27 : $i, X28 : $i]:
% 0.19/0.53         ((r1_tarski @ X27 @ X28) | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.53  thf('66', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C_2) @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.53  thf('67', plain, ($false),
% 0.19/0.53      inference('demod', [status(thm)], ['0', '57', '61', '66'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
