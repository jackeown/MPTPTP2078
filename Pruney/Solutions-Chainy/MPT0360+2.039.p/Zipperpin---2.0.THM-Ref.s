%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lH7QShYEjN

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:46 EST 2020

% Result     : Theorem 9.55s
% Output     : Refutation 9.55s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 820 expanded)
%              Number of leaves         :   25 ( 256 expanded)
%              Depth                    :   26
%              Number of atoms          : 1249 (6733 expanded)
%              Number of equality atoms :   84 ( 341 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( m1_subset_1 @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ( m1_subset_1 @ X25 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( v1_xboole_0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ( m1_subset_1 @ X25 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_subset_1 @ X1 @ k1_xboole_0 )
        = X1 )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ( ( k3_subset_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ( ( k3_subset_1 @ X1 @ k1_xboole_0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X1 @ k1_xboole_0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_subset_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_subset_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['13','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('54',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
        = ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('62',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('66',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('68',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
    = sk_B ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( r1_xboole_0 @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['67','88'])).

thf('90',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ sk_B )
      = ( k3_subset_1 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
      = sk_B )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
      = sk_B )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) )
      = sk_B ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','95'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( k1_xboole_0 = sk_B ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k3_subset_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','101'])).

thf('103',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v1_xboole_0 @ ( k3_subset_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_subset_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('111',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( m1_subset_1 @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('122',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('125',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','129'])).

thf('131',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','130'])).

thf('132',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['127','128'])).

thf('133',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('135',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['80','85'])).

thf('137',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('139',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['102','137','138'])).

thf('140',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['139','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lH7QShYEjN
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.55/9.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.55/9.76  % Solved by: fo/fo7.sh
% 9.55/9.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.55/9.76  % done 10785 iterations in 9.302s
% 9.55/9.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.55/9.76  % SZS output start Refutation
% 9.55/9.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.55/9.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.55/9.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.55/9.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.55/9.76  thf(sk_B_type, type, sk_B: $i).
% 9.55/9.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.55/9.76  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.55/9.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.55/9.76  thf(sk_A_type, type, sk_A: $i).
% 9.55/9.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.55/9.76  thf(sk_C_2_type, type, sk_C_2: $i).
% 9.55/9.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.55/9.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.55/9.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.55/9.76  thf('0', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 9.55/9.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.55/9.76  thf(t106_xboole_1, axiom,
% 9.55/9.76    (![A:$i,B:$i,C:$i]:
% 9.55/9.76     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 9.55/9.76       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 9.55/9.76  thf('1', plain,
% 9.55/9.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.55/9.76         ((r1_xboole_0 @ X6 @ X8)
% 9.55/9.76          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 9.55/9.76      inference('cnf', [status(esa)], [t106_xboole_1])).
% 9.55/9.76  thf('2', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 9.55/9.76      inference('sup-', [status(thm)], ['0', '1'])).
% 9.55/9.76  thf(t83_xboole_1, axiom,
% 9.55/9.76    (![A:$i,B:$i]:
% 9.55/9.76     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.55/9.76  thf('3', plain,
% 9.55/9.76      (![X12 : $i, X13 : $i]:
% 9.55/9.76         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 9.55/9.76      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.55/9.76  thf('4', plain,
% 9.55/9.76      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 9.55/9.76      inference('sup-', [status(thm)], ['2', '3'])).
% 9.55/9.76  thf(d3_tarski, axiom,
% 9.55/9.76    (![A:$i,B:$i]:
% 9.55/9.76     ( ( r1_tarski @ A @ B ) <=>
% 9.55/9.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 9.55/9.76  thf('5', plain,
% 9.55/9.76      (![X1 : $i, X3 : $i]:
% 9.55/9.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 9.55/9.76      inference('cnf', [status(esa)], [d3_tarski])).
% 9.55/9.76  thf('6', plain,
% 9.55/9.76      (![X1 : $i, X3 : $i]:
% 9.55/9.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 9.55/9.76      inference('cnf', [status(esa)], [d3_tarski])).
% 9.55/9.76  thf('7', plain,
% 9.55/9.76      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 9.55/9.76      inference('sup-', [status(thm)], ['5', '6'])).
% 9.55/9.76  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.55/9.76      inference('simplify', [status(thm)], ['7'])).
% 9.55/9.76  thf(t85_xboole_1, axiom,
% 9.55/9.76    (![A:$i,B:$i,C:$i]:
% 9.55/9.76     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 9.55/9.76  thf('9', plain,
% 9.55/9.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.55/9.76         (~ (r1_tarski @ X15 @ X16)
% 9.55/9.76          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 9.55/9.76      inference('cnf', [status(esa)], [t85_xboole_1])).
% 9.55/9.76  thf('10', plain,
% 9.55/9.76      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 9.55/9.76      inference('sup-', [status(thm)], ['8', '9'])).
% 9.55/9.76  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 9.55/9.76      inference('sup+', [status(thm)], ['4', '10'])).
% 9.55/9.76  thf('12', plain,
% 9.55/9.76      (![X12 : $i, X13 : $i]:
% 9.55/9.76         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 9.55/9.76      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.55/9.76  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.55/9.76      inference('sup-', [status(thm)], ['11', '12'])).
% 9.55/9.76  thf('14', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 9.55/9.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.55/9.76  thf(d1_zfmisc_1, axiom,
% 9.55/9.76    (![A:$i,B:$i]:
% 9.55/9.76     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 9.55/9.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 9.55/9.76  thf('15', plain,
% 9.55/9.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.55/9.76         (~ (r1_tarski @ X18 @ X19)
% 9.55/9.76          | (r2_hidden @ X18 @ X20)
% 9.55/9.76          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 9.55/9.76      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 9.55/9.76  thf('16', plain,
% 9.55/9.76      (![X18 : $i, X19 : $i]:
% 9.55/9.76         ((r2_hidden @ X18 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X18 @ X19))),
% 9.55/9.76      inference('simplify', [status(thm)], ['15'])).
% 9.55/9.76  thf('17', plain,
% 9.55/9.76      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.55/9.76      inference('sup-', [status(thm)], ['14', '16'])).
% 9.55/9.76  thf(d2_subset_1, axiom,
% 9.55/9.76    (![A:$i,B:$i]:
% 9.55/9.76     ( ( ( v1_xboole_0 @ A ) =>
% 9.55/9.76         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 9.55/9.76       ( ( ~( v1_xboole_0 @ A ) ) =>
% 9.55/9.76         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 9.55/9.76  thf('18', plain,
% 9.55/9.76      (![X23 : $i, X24 : $i]:
% 9.55/9.76         (~ (r2_hidden @ X23 @ X24)
% 9.55/9.76          | (m1_subset_1 @ X23 @ X24)
% 9.55/9.76          | (v1_xboole_0 @ X24))),
% 9.55/9.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.55/9.76  thf('19', plain,
% 9.55/9.76      (![X0 : $i]:
% 9.55/9.76         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 9.55/9.76      inference('sup-', [status(thm)], ['17', '18'])).
% 9.55/9.76  thf(d5_subset_1, axiom,
% 9.55/9.76    (![A:$i,B:$i]:
% 9.55/9.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.55/9.76       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.55/9.76  thf('20', plain,
% 9.55/9.76      (![X26 : $i, X27 : $i]:
% 9.55/9.76         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.55/9.76          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.55/9.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.55/9.76  thf('21', plain,
% 9.55/9.76      (![X0 : $i]:
% 9.55/9.76         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | ((k3_subset_1 @ X0 @ k1_xboole_0)
% 9.55/9.76              = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 9.55/9.76      inference('sup-', [status(thm)], ['19', '20'])).
% 9.55/9.76  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.55/9.76      inference('sup-', [status(thm)], ['11', '12'])).
% 9.55/9.76  thf('23', plain,
% 9.55/9.76      (![X0 : $i]:
% 9.55/9.76         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 9.55/9.76      inference('demod', [status(thm)], ['21', '22'])).
% 9.55/9.76  thf('24', plain,
% 9.55/9.76      (![X0 : $i]:
% 9.55/9.76         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 9.55/9.76      inference('demod', [status(thm)], ['21', '22'])).
% 9.55/9.76  thf('25', plain,
% 9.55/9.76      (![X24 : $i, X25 : $i]:
% 9.55/9.76         (~ (v1_xboole_0 @ X25)
% 9.55/9.76          | (m1_subset_1 @ X25 @ X24)
% 9.55/9.76          | ~ (v1_xboole_0 @ X24))),
% 9.55/9.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.55/9.76  thf(dt_k3_subset_1, axiom,
% 9.55/9.76    (![A:$i,B:$i]:
% 9.55/9.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.55/9.76       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.55/9.76  thf('26', plain,
% 9.55/9.76      (![X28 : $i, X29 : $i]:
% 9.55/9.76         ((m1_subset_1 @ (k3_subset_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 9.55/9.76          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 9.55/9.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.55/9.76  thf('27', plain,
% 9.55/9.76      (![X0 : $i, X1 : $i]:
% 9.55/9.76         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | ~ (v1_xboole_0 @ X1)
% 9.55/9.76          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 9.55/9.76      inference('sup-', [status(thm)], ['25', '26'])).
% 9.55/9.76  thf('28', plain,
% 9.55/9.76      (![X0 : $i, X1 : $i]:
% 9.55/9.76         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.76          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | ~ (v1_xboole_0 @ X1))),
% 9.55/9.76      inference('sup-', [status(thm)], ['24', '27'])).
% 9.55/9.76  thf('29', plain,
% 9.55/9.76      (![X24 : $i, X25 : $i]:
% 9.55/9.76         (~ (m1_subset_1 @ X25 @ X24)
% 9.55/9.76          | (v1_xboole_0 @ X25)
% 9.55/9.76          | ~ (v1_xboole_0 @ X24))),
% 9.55/9.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.55/9.76  thf('30', plain,
% 9.55/9.76      (![X0 : $i, X1 : $i]:
% 9.55/9.76         (~ (v1_xboole_0 @ X1)
% 9.55/9.76          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.76          | ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | (v1_xboole_0 @ (k3_subset_1 @ X0 @ X1)))),
% 9.55/9.76      inference('sup-', [status(thm)], ['28', '29'])).
% 9.55/9.76  thf('31', plain,
% 9.55/9.76      (![X0 : $i, X1 : $i]:
% 9.55/9.76         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.76          | (v1_xboole_0 @ (k3_subset_1 @ X0 @ X1))
% 9.55/9.76          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.76          | ~ (v1_xboole_0 @ X1))),
% 9.55/9.76      inference('sup-', [status(thm)], ['23', '30'])).
% 9.55/9.76  thf('32', plain,
% 9.55/9.76      (![X0 : $i, X1 : $i]:
% 9.55/9.76         (~ (v1_xboole_0 @ X1)
% 9.55/9.76          | (v1_xboole_0 @ (k3_subset_1 @ X0 @ X1))
% 9.55/9.76          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 9.55/9.76      inference('simplify', [status(thm)], ['31'])).
% 9.55/9.76  thf('33', plain,
% 9.55/9.76      (![X0 : $i]:
% 9.55/9.76         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 9.55/9.76      inference('demod', [status(thm)], ['21', '22'])).
% 9.55/9.76  thf('34', plain,
% 9.55/9.76      (![X24 : $i, X25 : $i]:
% 9.55/9.76         (~ (v1_xboole_0 @ X25)
% 9.55/9.76          | (m1_subset_1 @ X25 @ X24)
% 9.55/9.76          | ~ (v1_xboole_0 @ X24))),
% 9.55/9.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.55/9.76  thf(involutiveness_k3_subset_1, axiom,
% 9.55/9.76    (![A:$i,B:$i]:
% 9.55/9.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.55/9.76       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 9.55/9.76  thf('35', plain,
% 9.55/9.76      (![X30 : $i, X31 : $i]:
% 9.55/9.76         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 9.55/9.76          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 9.55/9.76      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.55/9.76  thf('36', plain,
% 9.55/9.76      (![X0 : $i, X1 : $i]:
% 9.55/9.76         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.76          | ~ (v1_xboole_0 @ X1)
% 9.55/9.76          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1)))),
% 9.55/9.76      inference('sup-', [status(thm)], ['34', '35'])).
% 9.55/9.77  thf('37', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.77          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1))
% 9.55/9.77          | ~ (v1_xboole_0 @ X1))),
% 9.55/9.77      inference('sup-', [status(thm)], ['33', '36'])).
% 9.55/9.77  thf('38', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.77          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ X1))),
% 9.55/9.77      inference('sup-', [status(thm)], ['24', '27'])).
% 9.55/9.77  thf('39', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0)
% 9.55/9.77          | ((k3_subset_1 @ X1 @ k1_xboole_0) = (X1))
% 9.55/9.77          | ~ (v1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 9.55/9.77          | ((k3_subset_1 @ X1 @ k1_xboole_0) = (X1)))),
% 9.55/9.77      inference('sup+', [status(thm)], ['37', '38'])).
% 9.55/9.77  thf('40', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (~ (v1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 9.55/9.77          | ((k3_subset_1 @ X1 @ k1_xboole_0) = (X1))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0)
% 9.55/9.77          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 9.55/9.77      inference('simplify', [status(thm)], ['39'])).
% 9.55/9.77  thf('41', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X1 @ k1_xboole_0) = (X1))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0)
% 9.55/9.77          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0)
% 9.55/9.77          | ((k3_subset_1 @ X1 @ k1_xboole_0) = (X1)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['32', '40'])).
% 9.55/9.77  thf('42', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0)
% 9.55/9.77          | ((k3_subset_1 @ X1 @ k1_xboole_0) = (X1)))),
% 9.55/9.77      inference('simplify', [status(thm)], ['41'])).
% 9.55/9.77  thf('43', plain,
% 9.55/9.77      (![X26 : $i, X27 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.55/9.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.55/9.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.55/9.77  thf('44', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ X1)
% 9.55/9.77          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['42', '43'])).
% 9.55/9.77  thf('45', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ k1_xboole_0)
% 9.55/9.77          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 9.55/9.77      inference('sup+', [status(thm)], ['13', '44'])).
% 9.55/9.77  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 9.55/9.77      inference('sup-', [status(thm)], ['0', '1'])).
% 9.55/9.77  thf(t69_xboole_1, axiom,
% 9.55/9.77    (![A:$i,B:$i]:
% 9.55/9.77     ( ( ~( v1_xboole_0 @ B ) ) =>
% 9.55/9.77       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 9.55/9.77  thf('47', plain,
% 9.55/9.77      (![X10 : $i, X11 : $i]:
% 9.55/9.77         (~ (r1_xboole_0 @ X10 @ X11)
% 9.55/9.77          | ~ (r1_tarski @ X10 @ X11)
% 9.55/9.77          | (v1_xboole_0 @ X10))),
% 9.55/9.77      inference('cnf', [status(esa)], [t69_xboole_1])).
% 9.55/9.77  thf('48', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['46', '47'])).
% 9.55/9.77  thf('49', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 9.55/9.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.55/9.77  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.55/9.77      inference('demod', [status(thm)], ['48', '49'])).
% 9.55/9.77  thf('51', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 9.55/9.77          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 9.55/9.77      inference('demod', [status(thm)], ['45', '50'])).
% 9.55/9.77  thf('52', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 9.55/9.77      inference('simplify', [status(thm)], ['51'])).
% 9.55/9.77  thf('53', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['17', '18'])).
% 9.55/9.77  thf('54', plain,
% 9.55/9.77      (![X30 : $i, X31 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 9.55/9.77          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 9.55/9.77      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.55/9.77  thf('55', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 9.55/9.77              = (k1_xboole_0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['53', '54'])).
% 9.55/9.77  thf('56', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['17', '18'])).
% 9.55/9.77  thf('57', plain,
% 9.55/9.77      (![X28 : $i, X29 : $i]:
% 9.55/9.77         ((m1_subset_1 @ (k3_subset_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 9.55/9.77          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 9.55/9.77      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.55/9.77  thf('58', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 9.55/9.77             (k1_zfmisc_1 @ X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['56', '57'])).
% 9.55/9.77  thf('59', plain,
% 9.55/9.77      (![X26 : $i, X27 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.55/9.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.55/9.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.55/9.77  thf('60', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 9.55/9.77              = (k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))))),
% 9.55/9.77      inference('sup-', [status(thm)], ['58', '59'])).
% 9.55/9.77  thf('61', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 9.55/9.77             (k1_zfmisc_1 @ X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['56', '57'])).
% 9.55/9.77  thf('62', plain,
% 9.55/9.77      (![X23 : $i, X24 : $i]:
% 9.55/9.77         (~ (m1_subset_1 @ X23 @ X24)
% 9.55/9.77          | (r2_hidden @ X23 @ X24)
% 9.55/9.77          | (v1_xboole_0 @ X24))),
% 9.55/9.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.55/9.77  thf('63', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (r2_hidden @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['61', '62'])).
% 9.55/9.77  thf('64', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((r2_hidden @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 9.55/9.77      inference('simplify', [status(thm)], ['63'])).
% 9.55/9.77  thf('65', plain,
% 9.55/9.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 9.55/9.77         (~ (r2_hidden @ X21 @ X20)
% 9.55/9.77          | (r1_tarski @ X21 @ X19)
% 9.55/9.77          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 9.55/9.77      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 9.55/9.77  thf('66', plain,
% 9.55/9.77      (![X19 : $i, X21 : $i]:
% 9.55/9.77         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 9.55/9.77      inference('simplify', [status(thm)], ['65'])).
% 9.55/9.77  thf('67', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['64', '66'])).
% 9.55/9.77  thf(t40_subset_1, conjecture,
% 9.55/9.77    (![A:$i,B:$i,C:$i]:
% 9.55/9.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.55/9.77       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 9.55/9.77         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.55/9.77  thf(zf_stmt_0, negated_conjecture,
% 9.55/9.77    (~( ![A:$i,B:$i,C:$i]:
% 9.55/9.77        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.55/9.77          ( ( ( r1_tarski @ B @ C ) & 
% 9.55/9.77              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 9.55/9.77            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 9.55/9.77    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 9.55/9.77  thf('68', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 9.55/9.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.55/9.77  thf('69', plain,
% 9.55/9.77      (![X26 : $i, X27 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.55/9.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.55/9.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.55/9.77  thf('70', plain,
% 9.55/9.77      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 9.55/9.77      inference('sup-', [status(thm)], ['68', '69'])).
% 9.55/9.77  thf('71', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['8', '9'])).
% 9.55/9.77  thf('72', plain,
% 9.55/9.77      (![X12 : $i, X13 : $i]:
% 9.55/9.77         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 9.55/9.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.55/9.77  thf('73', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['71', '72'])).
% 9.55/9.77  thf('74', plain,
% 9.55/9.77      (((k4_xboole_0 @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 9.55/9.77      inference('sup+', [status(thm)], ['70', '73'])).
% 9.55/9.77  thf('75', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 9.55/9.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.55/9.77  thf('76', plain,
% 9.55/9.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.55/9.77         (~ (r1_tarski @ X15 @ X16)
% 9.55/9.77          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 9.55/9.77      inference('cnf', [status(esa)], [t85_xboole_1])).
% 9.55/9.77  thf('77', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         (r1_xboole_0 @ sk_B @ 
% 9.55/9.77          (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['75', '76'])).
% 9.55/9.77  thf('78', plain,
% 9.55/9.77      (![X12 : $i, X13 : $i]:
% 9.55/9.77         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 9.55/9.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.55/9.77  thf('79', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((k4_xboole_0 @ sk_B @ 
% 9.55/9.77           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2))) = (sk_B))),
% 9.55/9.77      inference('sup-', [status(thm)], ['77', '78'])).
% 9.55/9.77  thf('80', plain, (((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))),
% 9.55/9.77      inference('sup+', [status(thm)], ['74', '79'])).
% 9.55/9.77  thf('81', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 9.55/9.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.55/9.77  thf('82', plain,
% 9.55/9.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.55/9.77         (~ (r1_tarski @ X15 @ X16)
% 9.55/9.77          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 9.55/9.77      inference('cnf', [status(esa)], [t85_xboole_1])).
% 9.55/9.77  thf('83', plain,
% 9.55/9.77      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2))),
% 9.55/9.77      inference('sup-', [status(thm)], ['81', '82'])).
% 9.55/9.77  thf('84', plain,
% 9.55/9.77      (![X12 : $i, X13 : $i]:
% 9.55/9.77         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 9.55/9.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.55/9.77  thf('85', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2)) = (sk_B))),
% 9.55/9.77      inference('sup-', [status(thm)], ['83', '84'])).
% 9.55/9.77  thf('86', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 9.55/9.77      inference('sup+', [status(thm)], ['80', '85'])).
% 9.55/9.77  thf('87', plain,
% 9.55/9.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.55/9.77         ((r1_xboole_0 @ X6 @ X8)
% 9.55/9.77          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 9.55/9.77      inference('cnf', [status(esa)], [t106_xboole_1])).
% 9.55/9.77  thf('88', plain,
% 9.55/9.77      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_B))),
% 9.55/9.77      inference('sup-', [status(thm)], ['86', '87'])).
% 9.55/9.77  thf('89', plain,
% 9.55/9.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77        | (r1_xboole_0 @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ sk_B))),
% 9.55/9.77      inference('sup-', [status(thm)], ['67', '88'])).
% 9.55/9.77  thf('90', plain,
% 9.55/9.77      (![X12 : $i, X13 : $i]:
% 9.55/9.77         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 9.55/9.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.55/9.77  thf('91', plain,
% 9.55/9.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77        | ((k4_xboole_0 @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ sk_B)
% 9.55/9.77            = (k3_subset_1 @ sk_B @ k1_xboole_0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['89', '90'])).
% 9.55/9.77  thf('92', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['71', '72'])).
% 9.55/9.77  thf('93', plain,
% 9.55/9.77      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ k1_xboole_0)) = (sk_B))
% 9.55/9.77        | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B)))),
% 9.55/9.77      inference('sup+', [status(thm)], ['91', '92'])).
% 9.55/9.77  thf('94', plain,
% 9.55/9.77      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ k1_xboole_0)) = (sk_B))
% 9.55/9.77        | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77        | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B)))),
% 9.55/9.77      inference('sup+', [status(thm)], ['60', '93'])).
% 9.55/9.77  thf('95', plain,
% 9.55/9.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77        | ((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ k1_xboole_0)) = (sk_B)))),
% 9.55/9.77      inference('simplify', [status(thm)], ['94'])).
% 9.55/9.77  thf('96', plain,
% 9.55/9.77      ((((k1_xboole_0) = (sk_B))
% 9.55/9.77        | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77        | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B)))),
% 9.55/9.77      inference('sup+', [status(thm)], ['55', '95'])).
% 9.55/9.77  thf('97', plain,
% 9.55/9.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B)) | ((k1_xboole_0) = (sk_B)))),
% 9.55/9.77      inference('simplify', [status(thm)], ['96'])).
% 9.55/9.77  thf('98', plain, (((sk_B) != (k1_xboole_0))),
% 9.55/9.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.55/9.77  thf('99', plain, ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))),
% 9.55/9.77      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 9.55/9.77  thf('100', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ X1)
% 9.55/9.77          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['34', '35'])).
% 9.55/9.77  thf('101', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ X0)) = (X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['99', '100'])).
% 9.55/9.77  thf('102', plain,
% 9.55/9.77      ((((k3_subset_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 9.55/9.77        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 9.55/9.77      inference('sup+', [status(thm)], ['52', '101'])).
% 9.55/9.77  thf('103', plain, ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))),
% 9.55/9.77      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 9.55/9.77  thf('104', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ X1)
% 9.55/9.77          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['25', '26'])).
% 9.55/9.77  thf('105', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((m1_subset_1 @ (k3_subset_1 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['103', '104'])).
% 9.55/9.77  thf('106', plain,
% 9.55/9.77      (![X24 : $i, X25 : $i]:
% 9.55/9.77         (~ (m1_subset_1 @ X25 @ X24)
% 9.55/9.77          | (v1_xboole_0 @ X25)
% 9.55/9.77          | ~ (v1_xboole_0 @ X24))),
% 9.55/9.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.55/9.77  thf('107', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         (~ (v1_xboole_0 @ X0)
% 9.55/9.77          | ~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77          | (v1_xboole_0 @ (k3_subset_1 @ sk_B @ X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['105', '106'])).
% 9.55/9.77  thf('108', plain, ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))),
% 9.55/9.77      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 9.55/9.77  thf('109', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_subset_1 @ sk_B @ X0)))),
% 9.55/9.77      inference('demod', [status(thm)], ['107', '108'])).
% 9.55/9.77  thf('110', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.55/9.77      inference('simplify', [status(thm)], ['7'])).
% 9.55/9.77  thf('111', plain,
% 9.55/9.77      (![X18 : $i, X19 : $i]:
% 9.55/9.77         ((r2_hidden @ X18 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X18 @ X19))),
% 9.55/9.77      inference('simplify', [status(thm)], ['15'])).
% 9.55/9.77  thf('112', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['110', '111'])).
% 9.55/9.77  thf('113', plain,
% 9.55/9.77      (![X23 : $i, X24 : $i]:
% 9.55/9.77         (~ (r2_hidden @ X23 @ X24)
% 9.55/9.77          | (m1_subset_1 @ X23 @ X24)
% 9.55/9.77          | (v1_xboole_0 @ X24))),
% 9.55/9.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.55/9.77  thf('114', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['112', '113'])).
% 9.55/9.77  thf('115', plain,
% 9.55/9.77      (![X30 : $i, X31 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 9.55/9.77          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 9.55/9.77      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.55/9.77  thf('116', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['114', '115'])).
% 9.55/9.77  thf('117', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ X1)
% 9.55/9.77          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['34', '35'])).
% 9.55/9.77  thf('118', plain,
% 9.55/9.77      (![X0 : $i, X1 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))
% 9.55/9.77          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1))
% 9.55/9.77          | ~ (v1_xboole_0 @ X1))),
% 9.55/9.77      inference('sup-', [status(thm)], ['116', '117'])).
% 9.55/9.77  thf('119', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         (((X0) != (X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0)
% 9.55/9.77          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0)))),
% 9.55/9.77      inference('eq_fact', [status(thm)], ['118'])).
% 9.55/9.77  thf('120', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0))),
% 9.55/9.77      inference('simplify', [status(thm)], ['119'])).
% 9.55/9.77  thf('121', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((m1_subset_1 @ (k3_subset_1 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77          | ~ (v1_xboole_0 @ X0))),
% 9.55/9.77      inference('sup-', [status(thm)], ['103', '104'])).
% 9.55/9.77  thf('122', plain,
% 9.55/9.77      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77        | ~ (v1_xboole_0 @ sk_B)
% 9.55/9.77        | ~ (v1_xboole_0 @ (k3_subset_1 @ sk_B @ sk_B)))),
% 9.55/9.77      inference('sup+', [status(thm)], ['120', '121'])).
% 9.55/9.77  thf('123', plain,
% 9.55/9.77      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 9.55/9.77      inference('sup-', [status(thm)], ['68', '69'])).
% 9.55/9.77  thf('124', plain,
% 9.55/9.77      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2))),
% 9.55/9.77      inference('sup-', [status(thm)], ['81', '82'])).
% 9.55/9.77  thf('125', plain,
% 9.55/9.77      (![X10 : $i, X11 : $i]:
% 9.55/9.77         (~ (r1_xboole_0 @ X10 @ X11)
% 9.55/9.77          | ~ (r1_tarski @ X10 @ X11)
% 9.55/9.77          | (v1_xboole_0 @ X10))),
% 9.55/9.77      inference('cnf', [status(esa)], [t69_xboole_1])).
% 9.55/9.77  thf('126', plain,
% 9.55/9.77      (![X0 : $i]:
% 9.55/9.77         ((v1_xboole_0 @ sk_B)
% 9.55/9.77          | ~ (r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['124', '125'])).
% 9.55/9.77  thf('127', plain,
% 9.55/9.77      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))
% 9.55/9.77        | (v1_xboole_0 @ sk_B))),
% 9.55/9.77      inference('sup-', [status(thm)], ['123', '126'])).
% 9.55/9.77  thf('128', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 9.55/9.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.55/9.77  thf('129', plain, ((v1_xboole_0 @ sk_B)),
% 9.55/9.77      inference('demod', [status(thm)], ['127', '128'])).
% 9.55/9.77  thf('130', plain,
% 9.55/9.77      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 9.55/9.77        | ~ (v1_xboole_0 @ (k3_subset_1 @ sk_B @ sk_B)))),
% 9.55/9.77      inference('demod', [status(thm)], ['122', '129'])).
% 9.55/9.77  thf('131', plain,
% 9.55/9.77      ((~ (v1_xboole_0 @ sk_B) | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B)))),
% 9.55/9.77      inference('sup-', [status(thm)], ['109', '130'])).
% 9.55/9.77  thf('132', plain, ((v1_xboole_0 @ sk_B)),
% 9.55/9.77      inference('demod', [status(thm)], ['127', '128'])).
% 9.55/9.77  thf('133', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))),
% 9.55/9.77      inference('demod', [status(thm)], ['131', '132'])).
% 9.55/9.77  thf('134', plain,
% 9.55/9.77      (![X26 : $i, X27 : $i]:
% 9.55/9.77         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.55/9.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.55/9.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.55/9.77  thf('135', plain,
% 9.55/9.77      (((k3_subset_1 @ sk_B @ sk_B) = (k4_xboole_0 @ sk_B @ sk_B))),
% 9.55/9.77      inference('sup-', [status(thm)], ['133', '134'])).
% 9.55/9.77  thf('136', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 9.55/9.77      inference('sup+', [status(thm)], ['80', '85'])).
% 9.55/9.77  thf('137', plain, (((k3_subset_1 @ sk_B @ sk_B) = (sk_B))),
% 9.55/9.77      inference('sup+', [status(thm)], ['135', '136'])).
% 9.55/9.77  thf('138', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.55/9.77      inference('demod', [status(thm)], ['48', '49'])).
% 9.55/9.77  thf('139', plain, (((sk_B) = (k1_xboole_0))),
% 9.55/9.77      inference('demod', [status(thm)], ['102', '137', '138'])).
% 9.55/9.77  thf('140', plain, (((sk_B) != (k1_xboole_0))),
% 9.55/9.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.55/9.77  thf('141', plain, ($false),
% 9.55/9.77      inference('simplify_reflect-', [status(thm)], ['139', '140'])).
% 9.55/9.77  
% 9.55/9.77  % SZS output end Refutation
% 9.55/9.77  
% 9.55/9.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
