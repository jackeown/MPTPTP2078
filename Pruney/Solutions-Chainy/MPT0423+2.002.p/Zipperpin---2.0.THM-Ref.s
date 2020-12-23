%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NDONP92Bmw

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:16 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 337 expanded)
%              Number of leaves         :   41 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          : 1133 (2721 expanded)
%              Number of equality atoms :   92 ( 285 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X49: $i] :
      ( ( k1_subset_1 @ X49 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X51 ) @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X73: $i,X74: $i] :
      ( ( r1_tarski @ X73 @ X74 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ X38 @ X39 )
      | ( r2_hidden @ X38 @ X40 )
      | ( X40
       != ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X38 @ X39 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X59 ) @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('10',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k7_setfam_1 @ X68 @ ( k7_setfam_1 @ X68 @ X67 ) )
        = X67 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t55_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B
          = ( k1_tarski @ A ) )
       => ( ( k7_setfam_1 @ A @ B )
          = ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B
            = ( k1_tarski @ A ) )
         => ( ( k7_setfam_1 @ A @ B )
            = ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X69 @ X70 ) )
      = ( k3_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_setfam_1 @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf(t51_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('21',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X82 ) ) )
      | ( r1_tarski @ X83 @ X81 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X82 @ X83 ) @ ( k7_setfam_1 @ X82 @ X81 ) )
      | ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X82 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
    | ( r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( k1_setfam_1 @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['13','18'])).

thf('29',plain,(
    r2_hidden @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('31',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k7_setfam_1 @ X68 @ ( k7_setfam_1 @ X68 @ X67 ) )
        = X67 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('32',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X62 ) ) )
      | ( X61
       != ( k7_setfam_1 @ X62 @ X63 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X62 @ X64 ) @ X63 )
      | ~ ( r2_hidden @ X64 @ X61 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('34',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X62 ) ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( r2_hidden @ X64 @ ( k7_setfam_1 @ X62 @ X63 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X62 @ X64 ) @ X63 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X62 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('37',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X65: $i,X66: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X65 @ X66 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X65 ) ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X65 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('41',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('44',plain,(
    ! [X78: $i,X79: $i,X80: $i] :
      ( ~ ( r2_hidden @ X78 @ X79 )
      | ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ X80 ) )
      | ( m1_subset_1 @ X78 @ X80 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_setfam_1 @ sk_B_1 ) ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','46'])).

thf('48',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X51 ) @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('49',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k3_subset_1 @ X53 @ ( k3_subset_1 @ X53 @ X52 ) )
        = X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k1_subset_1 @ X0 ) ) )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X49: $i] :
      ( ( k1_subset_1 @ X49 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('52',plain,(
    ! [X49: $i] :
      ( ( k1_subset_1 @ X49 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X54: $i] :
      ( ( k2_subset_1 @ X54 )
      = ( k3_subset_1 @ X54 @ ( k1_subset_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('55',plain,(
    ! [X50: $i] :
      ( ( k2_subset_1 @ X50 )
      = X50 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('56',plain,(
    ! [X54: $i] :
      ( X54
      = ( k3_subset_1 @ X54 @ ( k1_subset_1 @ X54 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X49: $i] :
      ( ( k1_subset_1 @ X49 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('60',plain,(
    r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','58','59'])).

thf('61',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X59 ) @ ( k1_zfmisc_1 @ X60 ) )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('62',plain,(
    m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X73: $i,X74: $i] :
      ( ( r1_tarski @ X73 @ X74 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('66',plain,(
    ! [X65: $i,X66: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X65 @ X66 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X65 ) ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X65 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['23','64','67'])).

thf('69',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('70',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44
        = ( k1_tarski @ X43 ) )
      | ( X44 = k1_xboole_0 )
      | ~ ( r1_tarski @ X44 @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      = sk_B_1 )
    | ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X76: $i,X77: $i] :
      ( ( ( k7_setfam_1 @ X76 @ X77 )
       != k1_xboole_0 )
      | ( X77 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X76 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('78',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47 != X46 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X46 ) )
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('79',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X46 ) )
     != ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('83',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('84',plain,(
    ! [X46: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X46 ) ) ),
    inference(demod,[status(thm)],['79','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['77','84'])).

thf('86',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('87',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t53_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( ( k7_setfam_1 @ A @ B )
              = ( k7_setfam_1 @ A @ C ) )
           => ( B = C ) ) ) ) )).

thf('88',plain,(
    ! [X84: $i,X85: $i,X86: $i] :
      ( ~ ( m1_subset_1 @ X84 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X85 ) ) )
      | ( X86 = X84 )
      | ( ( k7_setfam_1 @ X85 @ X86 )
       != ( k7_setfam_1 @ X85 @ X84 ) )
      | ~ ( m1_subset_1 @ X86 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X85 ) ) ) ) ),
    inference(cnf,[status(esa)],[t53_setfam_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k7_setfam_1 @ X0 @ X1 )
       != ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      | ( X1
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B_1
     != ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) )
    | ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k1_tarski @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('92',plain,
    ( ( sk_B_1
     != ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) )
    | ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B_1 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k1_setfam_1 @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['13','18'])).

thf('95',plain,(
    ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ sk_B_1 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    sk_B_1
 != ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['92','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','85','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NDONP92Bmw
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:38:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.90/2.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.90/2.09  % Solved by: fo/fo7.sh
% 1.90/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.90/2.09  % done 4298 iterations in 1.631s
% 1.90/2.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.90/2.09  % SZS output start Refutation
% 1.90/2.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.90/2.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.90/2.09  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.90/2.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.90/2.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.90/2.09  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.90/2.09  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.90/2.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.90/2.09  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.90/2.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.90/2.09  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.90/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.90/2.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.90/2.09  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 1.90/2.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.90/2.09  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.90/2.09  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.90/2.09  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.90/2.09  thf('0', plain, (![X49 : $i]: ((k1_subset_1 @ X49) = (k1_xboole_0))),
% 1.90/2.09      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.90/2.09  thf(dt_k1_subset_1, axiom,
% 1.90/2.09    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.90/2.09  thf('1', plain,
% 1.90/2.09      (![X51 : $i]: (m1_subset_1 @ (k1_subset_1 @ X51) @ (k1_zfmisc_1 @ X51))),
% 1.90/2.09      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 1.90/2.09  thf('2', plain,
% 1.90/2.09      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.90/2.09      inference('sup+', [status(thm)], ['0', '1'])).
% 1.90/2.09  thf(t3_subset, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.90/2.09  thf('3', plain,
% 1.90/2.09      (![X73 : $i, X74 : $i]:
% 1.90/2.09         ((r1_tarski @ X73 @ X74) | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ X74)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.90/2.09  thf('4', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.90/2.09      inference('sup-', [status(thm)], ['2', '3'])).
% 1.90/2.09  thf(d1_zfmisc_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.90/2.09       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.90/2.09  thf('5', plain,
% 1.90/2.09      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.90/2.09         (~ (r1_tarski @ X38 @ X39)
% 1.90/2.09          | (r2_hidden @ X38 @ X40)
% 1.90/2.09          | ((X40) != (k1_zfmisc_1 @ X39)))),
% 1.90/2.09      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.90/2.09  thf('6', plain,
% 1.90/2.09      (![X38 : $i, X39 : $i]:
% 1.90/2.09         ((r2_hidden @ X38 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X38 @ X39))),
% 1.90/2.09      inference('simplify', [status(thm)], ['5'])).
% 1.90/2.09  thf('7', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.90/2.09      inference('sup-', [status(thm)], ['4', '6'])).
% 1.90/2.09  thf(t63_subset_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( r2_hidden @ A @ B ) =>
% 1.90/2.09       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.90/2.09  thf('8', plain,
% 1.90/2.09      (![X59 : $i, X60 : $i]:
% 1.90/2.09         ((m1_subset_1 @ (k1_tarski @ X59) @ (k1_zfmisc_1 @ X60))
% 1.90/2.09          | ~ (r2_hidden @ X59 @ X60))),
% 1.90/2.09      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.90/2.09  thf('9', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.90/2.09          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['7', '8'])).
% 1.90/2.09  thf(involutiveness_k7_setfam_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 1.90/2.09  thf('10', plain,
% 1.90/2.09      (![X67 : $i, X68 : $i]:
% 1.90/2.09         (((k7_setfam_1 @ X68 @ (k7_setfam_1 @ X68 @ X67)) = (X67))
% 1.90/2.09          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X68))))),
% 1.90/2.09      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 1.90/2.09  thf('11', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 1.90/2.09           = (k1_tarski @ k1_xboole_0))),
% 1.90/2.09      inference('sup-', [status(thm)], ['9', '10'])).
% 1.90/2.09  thf(t55_setfam_1, conjecture,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09       ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 1.90/2.09         ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 1.90/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.90/2.09    (~( ![A:$i,B:$i]:
% 1.90/2.09        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09          ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 1.90/2.09            ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ) )),
% 1.90/2.09    inference('cnf.neg', [status(esa)], [t55_setfam_1])).
% 1.90/2.09  thf('12', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf('13', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(t69_enumset1, axiom,
% 1.90/2.09    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.90/2.09  thf('14', plain,
% 1.90/2.09      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 1.90/2.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.90/2.09  thf(t12_setfam_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.90/2.09  thf('15', plain,
% 1.90/2.09      (![X69 : $i, X70 : $i]:
% 1.90/2.09         ((k1_setfam_1 @ (k2_tarski @ X69 @ X70)) = (k3_xboole_0 @ X69 @ X70))),
% 1.90/2.09      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.90/2.09  thf('16', plain,
% 1.90/2.09      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 1.90/2.09      inference('sup+', [status(thm)], ['14', '15'])).
% 1.90/2.09  thf(idempotence_k3_xboole_0, axiom,
% 1.90/2.09    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.90/2.09  thf('17', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.90/2.09      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.90/2.09  thf('18', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 1.90/2.09      inference('demod', [status(thm)], ['16', '17'])).
% 1.90/2.09  thf('19', plain, (((k1_setfam_1 @ sk_B_1) = (sk_A))),
% 1.90/2.09      inference('sup+', [status(thm)], ['13', '18'])).
% 1.90/2.09  thf('20', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_B_1 @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.90/2.09      inference('demod', [status(thm)], ['12', '19'])).
% 1.90/2.09  thf(t51_setfam_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09       ( ![C:$i]:
% 1.90/2.09         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 1.90/2.09             ( r1_tarski @ B @ C ) ) ) ) ))).
% 1.90/2.09  thf('21', plain,
% 1.90/2.09      (![X81 : $i, X82 : $i, X83 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X82)))
% 1.90/2.09          | (r1_tarski @ X83 @ X81)
% 1.90/2.09          | ~ (r1_tarski @ (k7_setfam_1 @ X82 @ X83) @ 
% 1.90/2.09               (k7_setfam_1 @ X82 @ X81))
% 1.90/2.09          | ~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X82))))),
% 1.90/2.09      inference('cnf', [status(esa)], [t51_setfam_1])).
% 1.90/2.09  thf('22', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X0 @ 
% 1.90/2.09             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))
% 1.90/2.09          | ~ (r1_tarski @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.90/2.09               (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.90/2.09          | (r1_tarski @ X0 @ sk_B_1))),
% 1.90/2.09      inference('sup-', [status(thm)], ['20', '21'])).
% 1.90/2.09  thf('23', plain,
% 1.90/2.09      ((~ (r1_tarski @ (k1_tarski @ k1_xboole_0) @ 
% 1.90/2.09           (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.90/2.09        | (r1_tarski @ 
% 1.90/2.09           (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)) @ 
% 1.90/2.09           sk_B_1)
% 1.90/2.09        | ~ (m1_subset_1 @ 
% 1.90/2.09             (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)) @ 
% 1.90/2.09             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['11', '22'])).
% 1.90/2.09  thf('24', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(d1_tarski, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.90/2.09       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.90/2.09  thf('25', plain,
% 1.90/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.90/2.09         (((X6) != (X5)) | (r2_hidden @ X6 @ X7) | ((X7) != (k1_tarski @ X5)))),
% 1.90/2.09      inference('cnf', [status(esa)], [d1_tarski])).
% 1.90/2.09  thf('26', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_tarski @ X5))),
% 1.90/2.09      inference('simplify', [status(thm)], ['25'])).
% 1.90/2.09  thf('27', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 1.90/2.09      inference('sup+', [status(thm)], ['24', '26'])).
% 1.90/2.09  thf('28', plain, (((k1_setfam_1 @ sk_B_1) = (sk_A))),
% 1.90/2.09      inference('sup+', [status(thm)], ['13', '18'])).
% 1.90/2.09  thf('29', plain, ((r2_hidden @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)),
% 1.90/2.09      inference('demod', [status(thm)], ['27', '28'])).
% 1.90/2.09  thf('30', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_B_1 @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.90/2.09      inference('demod', [status(thm)], ['12', '19'])).
% 1.90/2.09  thf('31', plain,
% 1.90/2.09      (![X67 : $i, X68 : $i]:
% 1.90/2.09         (((k7_setfam_1 @ X68 @ (k7_setfam_1 @ X68 @ X67)) = (X67))
% 1.90/2.09          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X68))))),
% 1.90/2.09      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 1.90/2.09  thf('32', plain,
% 1.90/2.09      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ 
% 1.90/2.09         (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 1.90/2.09      inference('sup-', [status(thm)], ['30', '31'])).
% 1.90/2.09  thf(d8_setfam_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09       ( ![C:$i]:
% 1.90/2.09         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 1.90/2.09             ( ![D:$i]:
% 1.90/2.09               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.90/2.09                 ( ( r2_hidden @ D @ C ) <=>
% 1.90/2.09                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 1.90/2.09  thf('33', plain,
% 1.90/2.09      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X62)))
% 1.90/2.09          | ((X61) != (k7_setfam_1 @ X62 @ X63))
% 1.90/2.09          | (r2_hidden @ (k3_subset_1 @ X62 @ X64) @ X63)
% 1.90/2.09          | ~ (r2_hidden @ X64 @ X61)
% 1.90/2.09          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X62))
% 1.90/2.09          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X62))))),
% 1.90/2.09      inference('cnf', [status(esa)], [d8_setfam_1])).
% 1.90/2.09  thf('34', plain,
% 1.90/2.09      (![X62 : $i, X63 : $i, X64 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X62)))
% 1.90/2.09          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X62))
% 1.90/2.09          | ~ (r2_hidden @ X64 @ (k7_setfam_1 @ X62 @ X63))
% 1.90/2.09          | (r2_hidden @ (k3_subset_1 @ X62 @ X64) @ X63)
% 1.90/2.09          | ~ (m1_subset_1 @ (k7_setfam_1 @ X62 @ X63) @ 
% 1.90/2.09               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X62))))),
% 1.90/2.09      inference('simplify', [status(thm)], ['33'])).
% 1.90/2.09  thf('35', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ sk_B_1 @ 
% 1.90/2.09             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))
% 1.90/2.09          | (r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.90/2.09             (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.90/2.09          | ~ (r2_hidden @ X0 @ 
% 1.90/2.09               (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ 
% 1.90/2.09                (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)))
% 1.90/2.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))
% 1.90/2.09          | ~ (m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.90/2.09               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['32', '34'])).
% 1.90/2.09  thf('36', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_B_1 @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.90/2.09      inference('demod', [status(thm)], ['12', '19'])).
% 1.90/2.09  thf('37', plain,
% 1.90/2.09      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ 
% 1.90/2.09         (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 1.90/2.09      inference('sup-', [status(thm)], ['30', '31'])).
% 1.90/2.09  thf('38', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         ((r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.90/2.09           (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.90/2.09          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.90/2.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))
% 1.90/2.09          | ~ (m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.90/2.09               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))))),
% 1.90/2.09      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.90/2.09  thf('39', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_B_1 @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.90/2.09      inference('demod', [status(thm)], ['12', '19'])).
% 1.90/2.09  thf(dt_k7_setfam_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09       ( m1_subset_1 @
% 1.90/2.09         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.90/2.09  thf('40', plain,
% 1.90/2.09      (![X65 : $i, X66 : $i]:
% 1.90/2.09         ((m1_subset_1 @ (k7_setfam_1 @ X65 @ X66) @ 
% 1.90/2.09           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X65)))
% 1.90/2.09          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X65))))),
% 1.90/2.09      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.90/2.09  thf('41', plain,
% 1.90/2.09      ((m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['39', '40'])).
% 1.90/2.09  thf('42', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         ((r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.90/2.09           (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))
% 1.90/2.09          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.90/2.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.90/2.09      inference('demod', [status(thm)], ['38', '41'])).
% 1.90/2.09  thf('43', plain,
% 1.90/2.09      ((m1_subset_1 @ sk_B_1 @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.90/2.09      inference('demod', [status(thm)], ['12', '19'])).
% 1.90/2.09  thf(t4_subset, axiom,
% 1.90/2.09    (![A:$i,B:$i,C:$i]:
% 1.90/2.09     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.90/2.09       ( m1_subset_1 @ A @ C ) ))).
% 1.90/2.09  thf('44', plain,
% 1.90/2.09      (![X78 : $i, X79 : $i, X80 : $i]:
% 1.90/2.09         (~ (r2_hidden @ X78 @ X79)
% 1.90/2.09          | ~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ X80))
% 1.90/2.09          | (m1_subset_1 @ X78 @ X80))),
% 1.90/2.09      inference('cnf', [status(esa)], [t4_subset])).
% 1.90/2.09  thf('45', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))
% 1.90/2.09          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.90/2.09      inference('sup-', [status(thm)], ['43', '44'])).
% 1.90/2.09  thf('46', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.90/2.09          | (r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ X0) @ 
% 1.90/2.09             (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)))),
% 1.90/2.09      inference('clc', [status(thm)], ['42', '45'])).
% 1.90/2.09  thf('47', plain,
% 1.90/2.09      ((r2_hidden @ 
% 1.90/2.09        (k3_subset_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_setfam_1 @ sk_B_1)) @ 
% 1.90/2.09        (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))),
% 1.90/2.09      inference('sup-', [status(thm)], ['29', '46'])).
% 1.90/2.09  thf('48', plain,
% 1.90/2.09      (![X51 : $i]: (m1_subset_1 @ (k1_subset_1 @ X51) @ (k1_zfmisc_1 @ X51))),
% 1.90/2.09      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 1.90/2.09  thf(involutiveness_k3_subset_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.90/2.09       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.90/2.09  thf('49', plain,
% 1.90/2.09      (![X52 : $i, X53 : $i]:
% 1.90/2.09         (((k3_subset_1 @ X53 @ (k3_subset_1 @ X53 @ X52)) = (X52))
% 1.90/2.09          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53)))),
% 1.90/2.09      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.90/2.09  thf('50', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k1_subset_1 @ X0)))
% 1.90/2.09           = (k1_subset_1 @ X0))),
% 1.90/2.09      inference('sup-', [status(thm)], ['48', '49'])).
% 1.90/2.09  thf('51', plain, (![X49 : $i]: ((k1_subset_1 @ X49) = (k1_xboole_0))),
% 1.90/2.09      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.90/2.09  thf('52', plain, (![X49 : $i]: ((k1_subset_1 @ X49) = (k1_xboole_0))),
% 1.90/2.09      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.90/2.09  thf('53', plain,
% 1.90/2.09      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 1.90/2.09      inference('sup+', [status(thm)], ['51', '52'])).
% 1.90/2.09  thf(t22_subset_1, axiom,
% 1.90/2.09    (![A:$i]:
% 1.90/2.09     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.90/2.09  thf('54', plain,
% 1.90/2.09      (![X54 : $i]:
% 1.90/2.09         ((k2_subset_1 @ X54) = (k3_subset_1 @ X54 @ (k1_subset_1 @ X54)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.90/2.09  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.90/2.09  thf('55', plain, (![X50 : $i]: ((k2_subset_1 @ X50) = (X50))),
% 1.90/2.09      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.90/2.09  thf('56', plain,
% 1.90/2.09      (![X54 : $i]: ((X54) = (k3_subset_1 @ X54 @ (k1_subset_1 @ X54)))),
% 1.90/2.09      inference('demod', [status(thm)], ['54', '55'])).
% 1.90/2.09  thf('57', plain,
% 1.90/2.09      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 1.90/2.09      inference('sup+', [status(thm)], ['53', '56'])).
% 1.90/2.09  thf('58', plain,
% 1.90/2.09      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_subset_1 @ X0))),
% 1.90/2.09      inference('demod', [status(thm)], ['50', '57'])).
% 1.90/2.09  thf('59', plain, (![X49 : $i]: ((k1_subset_1 @ X49) = (k1_xboole_0))),
% 1.90/2.09      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.90/2.09  thf('60', plain,
% 1.90/2.09      ((r2_hidden @ k1_xboole_0 @ 
% 1.90/2.09        (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))),
% 1.90/2.09      inference('demod', [status(thm)], ['47', '58', '59'])).
% 1.90/2.09  thf('61', plain,
% 1.90/2.09      (![X59 : $i, X60 : $i]:
% 1.90/2.09         ((m1_subset_1 @ (k1_tarski @ X59) @ (k1_zfmisc_1 @ X60))
% 1.90/2.09          | ~ (r2_hidden @ X59 @ X60))),
% 1.90/2.09      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.90/2.09  thf('62', plain,
% 1.90/2.09      ((m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['60', '61'])).
% 1.90/2.09  thf('63', plain,
% 1.90/2.09      (![X73 : $i, X74 : $i]:
% 1.90/2.09         ((r1_tarski @ X73 @ X74) | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ X74)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t3_subset])).
% 1.90/2.09  thf('64', plain,
% 1.90/2.09      ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ 
% 1.90/2.09        (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1))),
% 1.90/2.09      inference('sup-', [status(thm)], ['62', '63'])).
% 1.90/2.09  thf('65', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.90/2.09          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['7', '8'])).
% 1.90/2.09  thf('66', plain,
% 1.90/2.09      (![X65 : $i, X66 : $i]:
% 1.90/2.09         ((m1_subset_1 @ (k7_setfam_1 @ X65 @ X66) @ 
% 1.90/2.09           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X65)))
% 1.90/2.09          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X65))))),
% 1.90/2.09      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.90/2.09  thf('67', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (m1_subset_1 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) @ 
% 1.90/2.09          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['65', '66'])).
% 1.90/2.09  thf('68', plain,
% 1.90/2.09      ((r1_tarski @ 
% 1.90/2.09        (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)) @ 
% 1.90/2.09        sk_B_1)),
% 1.90/2.09      inference('demod', [status(thm)], ['23', '64', '67'])).
% 1.90/2.09  thf('69', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf(l3_zfmisc_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.90/2.09       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.90/2.09  thf('70', plain,
% 1.90/2.09      (![X43 : $i, X44 : $i]:
% 1.90/2.09         (((X44) = (k1_tarski @ X43))
% 1.90/2.09          | ((X44) = (k1_xboole_0))
% 1.90/2.09          | ~ (r1_tarski @ X44 @ (k1_tarski @ X43)))),
% 1.90/2.09      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.90/2.09  thf('71', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (~ (r1_tarski @ X0 @ sk_B_1)
% 1.90/2.09          | ((X0) = (k1_xboole_0))
% 1.90/2.09          | ((X0) = (k1_tarski @ sk_A)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['69', '70'])).
% 1.90/2.09  thf('72', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf('73', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (~ (r1_tarski @ X0 @ sk_B_1)
% 1.90/2.09          | ((X0) = (k1_xboole_0))
% 1.90/2.09          | ((X0) = (sk_B_1)))),
% 1.90/2.09      inference('demod', [status(thm)], ['71', '72'])).
% 1.90/2.09  thf('74', plain,
% 1.90/2.09      ((((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0))
% 1.90/2.09          = (sk_B_1))
% 1.90/2.09        | ((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0))
% 1.90/2.09            = (k1_xboole_0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['68', '73'])).
% 1.90/2.09  thf('75', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.90/2.09          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['7', '8'])).
% 1.90/2.09  thf(t46_setfam_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.90/2.09            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.90/2.09  thf('76', plain,
% 1.90/2.09      (![X76 : $i, X77 : $i]:
% 1.90/2.09         (((k7_setfam_1 @ X76 @ X77) != (k1_xboole_0))
% 1.90/2.09          | ((X77) = (k1_xboole_0))
% 1.90/2.09          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X76))))),
% 1.90/2.09      inference('cnf', [status(esa)], [t46_setfam_1])).
% 1.90/2.09  thf('77', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 1.90/2.09          | ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['75', '76'])).
% 1.90/2.09  thf(t20_zfmisc_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.90/2.09         ( k1_tarski @ A ) ) <=>
% 1.90/2.09       ( ( A ) != ( B ) ) ))).
% 1.90/2.09  thf('78', plain,
% 1.90/2.09      (![X46 : $i, X47 : $i]:
% 1.90/2.09         (((X47) != (X46))
% 1.90/2.09          | ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X46))
% 1.90/2.09              != (k1_tarski @ X47)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.90/2.09  thf('79', plain,
% 1.90/2.09      (![X46 : $i]:
% 1.90/2.09         ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X46))
% 1.90/2.09           != (k1_tarski @ X46))),
% 1.90/2.09      inference('simplify', [status(thm)], ['78'])).
% 1.90/2.09  thf('80', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.90/2.09      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.90/2.09  thf(t100_xboole_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.90/2.09  thf('81', plain,
% 1.90/2.09      (![X2 : $i, X3 : $i]:
% 1.90/2.09         ((k4_xboole_0 @ X2 @ X3)
% 1.90/2.09           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.90/2.09      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.90/2.09  thf('82', plain,
% 1.90/2.09      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.90/2.09      inference('sup+', [status(thm)], ['80', '81'])).
% 1.90/2.09  thf(t92_xboole_1, axiom,
% 1.90/2.09    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.90/2.09  thf('83', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 1.90/2.09      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.90/2.09  thf('84', plain, (![X46 : $i]: ((k1_xboole_0) != (k1_tarski @ X46))),
% 1.90/2.09      inference('demod', [status(thm)], ['79', '82', '83'])).
% 1.90/2.09  thf('85', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0))),
% 1.90/2.09      inference('clc', [status(thm)], ['77', '84'])).
% 1.90/2.09  thf('86', plain,
% 1.90/2.09      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ 
% 1.90/2.09         (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 1.90/2.09      inference('sup-', [status(thm)], ['30', '31'])).
% 1.90/2.09  thf('87', plain,
% 1.90/2.09      (![X0 : $i]:
% 1.90/2.09         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.90/2.09          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['7', '8'])).
% 1.90/2.09  thf(t53_setfam_1, axiom,
% 1.90/2.09    (![A:$i,B:$i]:
% 1.90/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09       ( ![C:$i]:
% 1.90/2.09         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.90/2.09           ( ( ( k7_setfam_1 @ A @ B ) = ( k7_setfam_1 @ A @ C ) ) =>
% 1.90/2.09             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.90/2.09  thf('88', plain,
% 1.90/2.09      (![X84 : $i, X85 : $i, X86 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X84 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X85)))
% 1.90/2.09          | ((X86) = (X84))
% 1.90/2.09          | ((k7_setfam_1 @ X85 @ X86) != (k7_setfam_1 @ X85 @ X84))
% 1.90/2.09          | ~ (m1_subset_1 @ X86 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X85))))),
% 1.90/2.09      inference('cnf', [status(esa)], [t53_setfam_1])).
% 1.90/2.09  thf('89', plain,
% 1.90/2.09      (![X0 : $i, X1 : $i]:
% 1.90/2.09         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 1.90/2.09          | ((k7_setfam_1 @ X0 @ X1)
% 1.90/2.09              != (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 1.90/2.09          | ((X1) = (k1_tarski @ k1_xboole_0)))),
% 1.90/2.09      inference('sup-', [status(thm)], ['87', '88'])).
% 1.90/2.09  thf('90', plain,
% 1.90/2.09      ((((sk_B_1)
% 1.90/2.09          != (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)))
% 1.90/2.09        | ((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)
% 1.90/2.09            = (k1_tarski @ k1_xboole_0))
% 1.90/2.09        | ~ (m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.90/2.09             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1)))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['86', '89'])).
% 1.90/2.09  thf('91', plain,
% 1.90/2.09      ((m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1) @ 
% 1.90/2.09        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B_1))))),
% 1.90/2.09      inference('sup-', [status(thm)], ['39', '40'])).
% 1.90/2.09  thf('92', plain,
% 1.90/2.09      ((((sk_B_1)
% 1.90/2.09          != (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)))
% 1.90/2.09        | ((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)
% 1.90/2.09            = (k1_tarski @ k1_xboole_0)))),
% 1.90/2.09      inference('demod', [status(thm)], ['90', '91'])).
% 1.90/2.09  thf('93', plain,
% 1.90/2.09      (((k7_setfam_1 @ sk_A @ sk_B_1) != (k1_tarski @ k1_xboole_0))),
% 1.90/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.09  thf('94', plain, (((k1_setfam_1 @ sk_B_1) = (sk_A))),
% 1.90/2.09      inference('sup+', [status(thm)], ['13', '18'])).
% 1.90/2.09  thf('95', plain,
% 1.90/2.09      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ sk_B_1)
% 1.90/2.09         != (k1_tarski @ k1_xboole_0))),
% 1.90/2.09      inference('demod', [status(thm)], ['93', '94'])).
% 1.90/2.09  thf('96', plain,
% 1.90/2.09      (((sk_B_1)
% 1.90/2.09         != (k7_setfam_1 @ (k1_setfam_1 @ sk_B_1) @ (k1_tarski @ k1_xboole_0)))),
% 1.90/2.09      inference('simplify_reflect-', [status(thm)], ['92', '95'])).
% 1.90/2.09  thf('97', plain, ($false),
% 1.90/2.09      inference('simplify_reflect-', [status(thm)], ['74', '85', '96'])).
% 1.90/2.09  
% 1.90/2.09  % SZS output end Refutation
% 1.90/2.09  
% 1.93/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
