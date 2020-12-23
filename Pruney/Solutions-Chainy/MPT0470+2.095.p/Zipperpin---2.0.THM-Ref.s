%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l5uDGGOim2

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:40 EST 2020

% Result     : Theorem 5.61s
% Output     : Refutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 128 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   19
%              Number of atoms          :  877 (1322 expanded)
%              Number of equality atoms :   46 (  89 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X18 @ X16 @ X17 ) @ ( sk_E @ X18 @ X16 @ X17 ) ) @ X18 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X18 @ X16 @ X17 ) @ ( sk_E @ X18 @ X16 @ X17 ) ) @ X16 )
      | ( X18
        = ( k5_relat_1 @ X17 @ X16 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X2 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X3 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X18 @ X16 @ X17 ) @ ( sk_E @ X18 @ X16 @ X17 ) ) @ X18 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X18 @ X16 @ X17 ) @ ( sk_F @ X18 @ X16 @ X17 ) ) @ X17 )
      | ( X18
        = ( k5_relat_1 @ X17 @ X16 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_E @ X0 @ X2 @ X1 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_F @ k1_xboole_0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X2 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('46',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('51',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','51'])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l5uDGGOim2
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:47:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 5.61/5.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.61/5.87  % Solved by: fo/fo7.sh
% 5.61/5.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.61/5.87  % done 674 iterations in 5.414s
% 5.61/5.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.61/5.87  % SZS output start Refutation
% 5.61/5.87  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.61/5.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.61/5.87  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 5.61/5.87  thf(sk_A_type, type, sk_A: $i).
% 5.61/5.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.61/5.87  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.61/5.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.61/5.87  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 5.61/5.87  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 5.61/5.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.61/5.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.61/5.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.61/5.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.61/5.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.61/5.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.61/5.87  thf('0', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.61/5.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.61/5.87  thf('1', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.61/5.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.61/5.87  thf(d8_relat_1, axiom,
% 5.61/5.87    (![A:$i]:
% 5.61/5.87     ( ( v1_relat_1 @ A ) =>
% 5.61/5.87       ( ![B:$i]:
% 5.61/5.87         ( ( v1_relat_1 @ B ) =>
% 5.61/5.87           ( ![C:$i]:
% 5.61/5.87             ( ( v1_relat_1 @ C ) =>
% 5.61/5.87               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 5.61/5.87                 ( ![D:$i,E:$i]:
% 5.61/5.87                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 5.61/5.87                     ( ?[F:$i]:
% 5.61/5.87                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 5.61/5.87                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 5.61/5.87  thf('2', plain,
% 5.61/5.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X16)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X18 @ X16 @ X17) @ (sk_E @ X18 @ X16 @ X17)) @ 
% 5.61/5.87             X18)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ X18 @ X16 @ X17) @ (sk_E @ X18 @ X16 @ X17)) @ 
% 5.61/5.87             X16)
% 5.61/5.87          | ((X18) = (k5_relat_1 @ X17 @ X16))
% 5.61/5.87          | ~ (v1_relat_1 @ X18)
% 5.61/5.87          | ~ (v1_relat_1 @ X17))),
% 5.61/5.87      inference('cnf', [status(esa)], [d8_relat_1])).
% 5.61/5.87  thf(d3_relat_1, axiom,
% 5.61/5.87    (![A:$i]:
% 5.61/5.87     ( ( v1_relat_1 @ A ) =>
% 5.61/5.87       ( ![B:$i]:
% 5.61/5.87         ( ( r1_tarski @ A @ B ) <=>
% 5.61/5.87           ( ![C:$i,D:$i]:
% 5.61/5.87             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 5.61/5.87               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 5.61/5.87  thf('3', plain,
% 5.61/5.87      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.61/5.87         (~ (r1_tarski @ X12 @ X13)
% 5.61/5.87          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 5.61/5.87          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X12)
% 5.61/5.87          | ~ (v1_relat_1 @ X12))),
% 5.61/5.87      inference('cnf', [status(esa)], [d3_relat_1])).
% 5.61/5.87  thf('4', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 5.61/5.87          | ~ (v1_relat_1 @ X2)
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 5.61/5.87          | ~ (r1_tarski @ X0 @ X3))),
% 5.61/5.87      inference('sup-', [status(thm)], ['2', '3'])).
% 5.61/5.87  thf('5', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.87         (~ (r1_tarski @ X0 @ X3)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 5.61/5.87          | ~ (v1_relat_1 @ X2)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X2)
% 5.61/5.87          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | ~ (v1_relat_1 @ X1))),
% 5.61/5.87      inference('simplify', [status(thm)], ['4'])).
% 5.61/5.87  thf('6', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ~ (v1_relat_1 @ k1_xboole_0)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 5.61/5.87             X2)
% 5.61/5.87          | ~ (v1_relat_1 @ X2)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 5.61/5.87             X0))),
% 5.61/5.87      inference('sup-', [status(thm)], ['1', '5'])).
% 5.61/5.87  thf(t62_relat_1, conjecture,
% 5.61/5.87    (![A:$i]:
% 5.61/5.87     ( ( v1_relat_1 @ A ) =>
% 5.61/5.87       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 5.61/5.87         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 5.61/5.87  thf(zf_stmt_0, negated_conjecture,
% 5.61/5.87    (~( ![A:$i]:
% 5.61/5.87        ( ( v1_relat_1 @ A ) =>
% 5.61/5.87          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 5.61/5.87            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 5.61/5.87    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 5.61/5.87  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 5.61/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.61/5.87  thf(t4_subset_1, axiom,
% 5.61/5.87    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.61/5.87  thf('8', plain,
% 5.61/5.87      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 5.61/5.87      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.61/5.87  thf(cc2_relat_1, axiom,
% 5.61/5.87    (![A:$i]:
% 5.61/5.87     ( ( v1_relat_1 @ A ) =>
% 5.61/5.87       ( ![B:$i]:
% 5.61/5.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.61/5.87  thf('9', plain,
% 5.61/5.87      (![X9 : $i, X10 : $i]:
% 5.61/5.87         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 5.61/5.87          | (v1_relat_1 @ X9)
% 5.61/5.87          | ~ (v1_relat_1 @ X10))),
% 5.61/5.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.61/5.87  thf('10', plain,
% 5.61/5.87      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 5.61/5.87      inference('sup-', [status(thm)], ['8', '9'])).
% 5.61/5.87  thf('11', plain, ((v1_relat_1 @ k1_xboole_0)),
% 5.61/5.87      inference('sup-', [status(thm)], ['7', '10'])).
% 5.61/5.87  thf('12', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ k1_xboole_0 @ X2 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 5.61/5.87             X2)
% 5.61/5.87          | ~ (v1_relat_1 @ X2)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 5.61/5.87             X0))),
% 5.61/5.87      inference('demod', [status(thm)], ['6', '11'])).
% 5.61/5.87  thf(t64_zfmisc_1, axiom,
% 5.61/5.87    (![A:$i,B:$i,C:$i]:
% 5.61/5.87     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 5.61/5.87       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 5.61/5.87  thf('13', plain,
% 5.61/5.87      (![X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.87         (((X1) != (X3))
% 5.61/5.87          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X3))))),
% 5.61/5.87      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 5.61/5.87  thf('14', plain,
% 5.61/5.87      (![X2 : $i, X3 : $i]:
% 5.61/5.87         ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X3)))),
% 5.61/5.87      inference('simplify', [status(thm)], ['13'])).
% 5.61/5.87  thf('15', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 5.61/5.87             X1)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 5.61/5.87          | ~ (v1_relat_1 @ X0))),
% 5.61/5.87      inference('sup-', [status(thm)], ['12', '14'])).
% 5.61/5.87  thf('16', plain,
% 5.61/5.87      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.61/5.87         (~ (r1_tarski @ X12 @ X13)
% 5.61/5.87          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 5.61/5.87          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X12)
% 5.61/5.87          | ~ (v1_relat_1 @ X12))),
% 5.61/5.87      inference('cnf', [status(esa)], [d3_relat_1])).
% 5.61/5.87  thf('17', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 5.61/5.87             X2)
% 5.61/5.87          | ~ (r1_tarski @ X0 @ X2))),
% 5.61/5.87      inference('sup-', [status(thm)], ['15', '16'])).
% 5.61/5.87  thf('18', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.87         (~ (r1_tarski @ X0 @ X2)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 5.61/5.87             X2)
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 5.61/5.87          | ~ (v1_relat_1 @ X1))),
% 5.61/5.87      inference('simplify', [status(thm)], ['17'])).
% 5.61/5.87  thf('19', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 5.61/5.87          | ~ (v1_relat_1 @ k1_xboole_0)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1)) @ 
% 5.61/5.87             X0))),
% 5.61/5.87      inference('sup-', [status(thm)], ['0', '18'])).
% 5.61/5.87  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 5.61/5.87      inference('sup-', [status(thm)], ['7', '10'])).
% 5.61/5.87  thf('21', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0))
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_F @ k1_xboole_0 @ k1_xboole_0 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X1)) @ 
% 5.61/5.87             X0))),
% 5.61/5.87      inference('demod', [status(thm)], ['19', '20'])).
% 5.61/5.87  thf('22', plain,
% 5.61/5.87      (![X2 : $i, X3 : $i]:
% 5.61/5.87         ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X3)))),
% 5.61/5.87      inference('simplify', [status(thm)], ['13'])).
% 5.61/5.87  thf('23', plain,
% 5.61/5.87      (![X0 : $i]:
% 5.61/5.87         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 5.61/5.87          | ~ (v1_relat_1 @ X0))),
% 5.61/5.87      inference('sup-', [status(thm)], ['21', '22'])).
% 5.61/5.87  thf('24', plain,
% 5.61/5.87      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 5.61/5.87        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 5.61/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.61/5.87  thf('25', plain,
% 5.61/5.87      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 5.61/5.87         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 5.61/5.87      inference('split', [status(esa)], ['24'])).
% 5.61/5.87  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.61/5.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.61/5.87  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.61/5.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.61/5.87  thf('28', plain,
% 5.61/5.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X16)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X18 @ X16 @ X17) @ (sk_E @ X18 @ X16 @ X17)) @ 
% 5.61/5.87             X18)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X18 @ X16 @ X17) @ (sk_F @ X18 @ X16 @ X17)) @ 
% 5.61/5.87             X17)
% 5.61/5.87          | ((X18) = (k5_relat_1 @ X17 @ X16))
% 5.61/5.87          | ~ (v1_relat_1 @ X18)
% 5.61/5.87          | ~ (v1_relat_1 @ X17))),
% 5.61/5.87      inference('cnf', [status(esa)], [d8_relat_1])).
% 5.61/5.87  thf('29', plain,
% 5.61/5.87      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.61/5.87         (~ (r1_tarski @ X12 @ X13)
% 5.61/5.87          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 5.61/5.87          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X12)
% 5.61/5.87          | ~ (v1_relat_1 @ X12))),
% 5.61/5.87      inference('cnf', [status(esa)], [d3_relat_1])).
% 5.61/5.87  thf('30', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 5.61/5.87          | ~ (v1_relat_1 @ X2)
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 5.61/5.87          | ~ (r1_tarski @ X0 @ X3))),
% 5.61/5.87      inference('sup-', [status(thm)], ['28', '29'])).
% 5.61/5.87  thf('31', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.61/5.87         (~ (r1_tarski @ X0 @ X3)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_E @ X0 @ X2 @ X1)) @ X3)
% 5.61/5.87          | ~ (v1_relat_1 @ X2)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 5.61/5.87          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | ~ (v1_relat_1 @ X1))),
% 5.61/5.87      inference('simplify', [status(thm)], ['30'])).
% 5.61/5.87  thf('32', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ~ (v1_relat_1 @ k1_xboole_0)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 5.61/5.87              (sk_F @ k1_xboole_0 @ X2 @ X1)) @ 
% 5.61/5.87             X1)
% 5.61/5.87          | ~ (v1_relat_1 @ X2)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 5.61/5.87             X0))),
% 5.61/5.87      inference('sup-', [status(thm)], ['27', '31'])).
% 5.61/5.87  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 5.61/5.87      inference('sup-', [status(thm)], ['7', '10'])).
% 5.61/5.87  thf('34', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X2))
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 5.61/5.87              (sk_F @ k1_xboole_0 @ X2 @ X1)) @ 
% 5.61/5.87             X1)
% 5.61/5.87          | ~ (v1_relat_1 @ X2)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X2 @ X1) @ 
% 5.61/5.87              (sk_E @ k1_xboole_0 @ X2 @ X1)) @ 
% 5.61/5.87             X0))),
% 5.61/5.87      inference('demod', [status(thm)], ['32', '33'])).
% 5.61/5.87  thf('35', plain,
% 5.61/5.87      (![X2 : $i, X3 : $i]:
% 5.61/5.87         ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X3)))),
% 5.61/5.87      inference('simplify', [status(thm)], ['13'])).
% 5.61/5.87  thf('36', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X1)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 5.61/5.87              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 5.61/5.87             X0)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 5.61/5.87          | ~ (v1_relat_1 @ X0))),
% 5.61/5.87      inference('sup-', [status(thm)], ['34', '35'])).
% 5.61/5.87  thf('37', plain,
% 5.61/5.87      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.61/5.87         (~ (r1_tarski @ X12 @ X13)
% 5.61/5.87          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X13)
% 5.61/5.87          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X12)
% 5.61/5.87          | ~ (v1_relat_1 @ X12))),
% 5.61/5.87      inference('cnf', [status(esa)], [d3_relat_1])).
% 5.61/5.87  thf('38', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X0)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 5.61/5.87          | ~ (v1_relat_1 @ X1)
% 5.61/5.87          | ~ (v1_relat_1 @ X0)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 5.61/5.87              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 5.61/5.87             X2)
% 5.61/5.87          | ~ (r1_tarski @ X0 @ X2))),
% 5.61/5.87      inference('sup-', [status(thm)], ['36', '37'])).
% 5.61/5.87  thf('39', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.61/5.87         (~ (r1_tarski @ X0 @ X2)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ X0) @ 
% 5.61/5.87              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 5.61/5.87             X2)
% 5.61/5.87          | ~ (v1_relat_1 @ X1)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 5.61/5.87          | ~ (v1_relat_1 @ X0))),
% 5.61/5.87      inference('simplify', [status(thm)], ['38'])).
% 5.61/5.87  thf('40', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ k1_xboole_0)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1))
% 5.61/5.87          | ~ (v1_relat_1 @ X1)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) @ 
% 5.61/5.87              (sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0)) @ 
% 5.61/5.87             X0))),
% 5.61/5.87      inference('sup-', [status(thm)], ['26', '39'])).
% 5.61/5.87  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 5.61/5.87      inference('sup-', [status(thm)], ['7', '10'])).
% 5.61/5.87  thf('42', plain,
% 5.61/5.87      (![X0 : $i, X1 : $i]:
% 5.61/5.87         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1))
% 5.61/5.87          | ~ (v1_relat_1 @ X1)
% 5.61/5.87          | (r2_hidden @ 
% 5.61/5.87             (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) @ 
% 5.61/5.87              (sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0)) @ 
% 5.61/5.87             X0))),
% 5.61/5.87      inference('demod', [status(thm)], ['40', '41'])).
% 5.61/5.87  thf('43', plain,
% 5.61/5.87      (![X2 : $i, X3 : $i]:
% 5.61/5.87         ~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X3)))),
% 5.61/5.87      inference('simplify', [status(thm)], ['13'])).
% 5.61/5.87  thf('44', plain,
% 5.61/5.87      (![X0 : $i]:
% 5.61/5.87         (~ (v1_relat_1 @ X0)
% 5.61/5.87          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 5.61/5.87      inference('sup-', [status(thm)], ['42', '43'])).
% 5.61/5.87  thf('45', plain,
% 5.61/5.87      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 5.61/5.87         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 5.61/5.87      inference('split', [status(esa)], ['24'])).
% 5.61/5.87  thf('46', plain,
% 5.61/5.87      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 5.61/5.87         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 5.61/5.87      inference('sup-', [status(thm)], ['44', '45'])).
% 5.61/5.87  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 5.61/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.61/5.87  thf('48', plain,
% 5.61/5.87      ((((k1_xboole_0) != (k1_xboole_0)))
% 5.61/5.87         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 5.61/5.87      inference('demod', [status(thm)], ['46', '47'])).
% 5.61/5.87  thf('49', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 5.61/5.87      inference('simplify', [status(thm)], ['48'])).
% 5.61/5.87  thf('50', plain,
% 5.61/5.87      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 5.61/5.87       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 5.61/5.87      inference('split', [status(esa)], ['24'])).
% 5.61/5.87  thf('51', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 5.61/5.87      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 5.61/5.87  thf('52', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 5.61/5.87      inference('simpl_trail', [status(thm)], ['25', '51'])).
% 5.61/5.87  thf('53', plain,
% 5.61/5.87      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 5.61/5.87      inference('sup-', [status(thm)], ['23', '52'])).
% 5.61/5.87  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 5.61/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.61/5.87  thf('55', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 5.61/5.87      inference('demod', [status(thm)], ['53', '54'])).
% 5.61/5.87  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 5.61/5.87  
% 5.61/5.87  % SZS output end Refutation
% 5.61/5.87  
% 5.61/5.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
