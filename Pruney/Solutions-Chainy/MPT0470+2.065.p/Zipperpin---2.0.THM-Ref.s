%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iTxHQ1X8J

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:35 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 448 expanded)
%              Number of leaves         :   32 ( 153 expanded)
%              Depth                    :   32
%              Number of atoms          :  898 (3000 expanded)
%              Number of equality atoms :   78 ( 224 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X20 @ X19 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X20 ) @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X20 @ X19 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X20 ) @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','49'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X23 ) @ ( k4_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

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

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('71',plain,(
    ! [X18: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','49'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','64'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('80',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('88',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['80'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['80'])).

thf('99',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['82','99'])).

thf('101',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    $false ),
    inference(simplify,[status(thm)],['104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iTxHQ1X8J
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:45:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.83/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.06  % Solved by: fo/fo7.sh
% 0.83/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.06  % done 1255 iterations in 0.618s
% 0.83/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.06  % SZS output start Refutation
% 0.83/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.83/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.06  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.83/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.06  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.83/1.06  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.83/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.06  thf(dt_k5_relat_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.83/1.06       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.83/1.06  thf('0', plain,
% 0.83/1.06      (![X15 : $i, X16 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X15)
% 0.83/1.06          | ~ (v1_relat_1 @ X16)
% 0.83/1.06          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.83/1.06  thf(dt_k4_relat_1, axiom,
% 0.83/1.06    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.83/1.06  thf('1', plain,
% 0.83/1.06      (![X14 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X14)) | ~ (v1_relat_1 @ X14))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.83/1.06  thf(l13_xboole_0, axiom,
% 0.83/1.06    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.83/1.06  thf('2', plain,
% 0.83/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf(cc1_relat_1, axiom,
% 0.83/1.06    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.83/1.06  thf('3', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.83/1.06      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.83/1.06  thf('4', plain,
% 0.83/1.06      (![X15 : $i, X16 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X15)
% 0.83/1.06          | ~ (v1_relat_1 @ X16)
% 0.83/1.06          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.83/1.06  thf('5', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.83/1.06      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.83/1.06  thf(t60_relat_1, axiom,
% 0.83/1.06    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.83/1.06     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.83/1.06  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.06      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.83/1.06  thf(t46_relat_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( v1_relat_1 @ A ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( v1_relat_1 @ B ) =>
% 0.83/1.06           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.83/1.06             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.83/1.06  thf('7', plain,
% 0.83/1.06      (![X21 : $i, X22 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X21)
% 0.83/1.06          | ((k1_relat_1 @ (k5_relat_1 @ X22 @ X21)) = (k1_relat_1 @ X22))
% 0.83/1.06          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X21))
% 0.83/1.06          | ~ (v1_relat_1 @ X22))),
% 0.83/1.06      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.83/1.06  thf('8', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.83/1.06          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.06          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.06              = (k1_relat_1 @ k1_xboole_0))
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.06  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.83/1.06  thf('9', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.83/1.06      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.83/1.06  thf('10', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.06      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.83/1.06  thf('11', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.06          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.83/1.06  thf('12', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['5', '11'])).
% 0.83/1.06  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.06  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.06  thf('14', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0)
% 0.83/1.06          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['12', '13'])).
% 0.83/1.06  thf(fc8_relat_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.83/1.06       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.83/1.06  thf('15', plain,
% 0.83/1.06      (![X17 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ (k1_relat_1 @ X17))
% 0.83/1.06          | ~ (v1_relat_1 @ X17)
% 0.83/1.06          | (v1_xboole_0 @ X17))),
% 0.83/1.06      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.83/1.06  thf('16', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.06          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['14', '15'])).
% 0.83/1.06  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.06  thf('18', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0)
% 0.83/1.06          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.06          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['16', '17'])).
% 0.83/1.06  thf('19', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.06          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['4', '18'])).
% 0.83/1.06  thf('20', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.83/1.06          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('simplify', [status(thm)], ['19'])).
% 0.83/1.06  thf('21', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['3', '20'])).
% 0.83/1.06  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.06  thf('23', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.83/1.06  thf('24', plain,
% 0.83/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf('25', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0)
% 0.83/1.06          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['23', '24'])).
% 0.83/1.06  thf('26', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.83/1.06          | ~ (v1_xboole_0 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ X1))),
% 0.83/1.06      inference('sup+', [status(thm)], ['2', '25'])).
% 0.83/1.06  thf('27', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_xboole_0 @ X1)
% 0.83/1.06          | ((k5_relat_1 @ X1 @ (k4_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['1', '26'])).
% 0.83/1.06  thf(dt_k6_subset_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.83/1.06  thf('28', plain,
% 0.83/1.06      (![X6 : $i, X7 : $i]:
% 0.83/1.06         (m1_subset_1 @ (k6_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.83/1.06  thf(redefinition_k6_subset_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.83/1.06  thf('29', plain,
% 0.83/1.06      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.83/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.06  thf('30', plain,
% 0.83/1.06      (![X6 : $i, X7 : $i]:
% 0.83/1.06         (m1_subset_1 @ (k4_xboole_0 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))),
% 0.83/1.06      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.06  thf(t3_subset, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.06  thf('31', plain,
% 0.83/1.06      (![X10 : $i, X11 : $i]:
% 0.83/1.06         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.83/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.06  thf('32', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.83/1.06      inference('sup-', [status(thm)], ['30', '31'])).
% 0.83/1.06  thf(t79_xboole_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.83/1.06  thf('33', plain,
% 0.83/1.06      (![X4 : $i, X5 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X5)),
% 0.83/1.06      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.83/1.06  thf(t69_xboole_1, axiom,
% 0.83/1.06    (![A:$i,B:$i]:
% 0.83/1.06     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.83/1.06       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.83/1.06  thf('34', plain,
% 0.83/1.06      (![X2 : $i, X3 : $i]:
% 0.83/1.06         (~ (r1_xboole_0 @ X2 @ X3)
% 0.83/1.06          | ~ (r1_tarski @ X2 @ X3)
% 0.83/1.06          | (v1_xboole_0 @ X2))),
% 0.83/1.06      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.83/1.06  thf('35', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.83/1.06          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['33', '34'])).
% 0.83/1.06  thf('36', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['32', '35'])).
% 0.83/1.06  thf('37', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.83/1.06      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.83/1.06  thf('38', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['32', '35'])).
% 0.83/1.06  thf('39', plain,
% 0.83/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['38', '39'])).
% 0.83/1.06  thf(t41_relat_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( v1_relat_1 @ A ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( v1_relat_1 @ B ) =>
% 0.83/1.06           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.83/1.06             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.83/1.06  thf('41', plain,
% 0.83/1.06      (![X19 : $i, X20 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X19)
% 0.83/1.06          | ((k4_relat_1 @ (k6_subset_1 @ X20 @ X19))
% 0.83/1.06              = (k6_subset_1 @ (k4_relat_1 @ X20) @ (k4_relat_1 @ X19)))
% 0.83/1.06          | ~ (v1_relat_1 @ X20))),
% 0.83/1.06      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.83/1.06  thf('42', plain,
% 0.83/1.06      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.83/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.06  thf('43', plain,
% 0.83/1.06      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.83/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.06  thf('44', plain,
% 0.83/1.06      (![X19 : $i, X20 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X19)
% 0.83/1.06          | ((k4_relat_1 @ (k4_xboole_0 @ X20 @ X19))
% 0.83/1.06              = (k4_xboole_0 @ (k4_relat_1 @ X20) @ (k4_relat_1 @ X19)))
% 0.83/1.06          | ~ (v1_relat_1 @ X20))),
% 0.83/1.06      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.83/1.06  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['38', '39'])).
% 0.83/1.06  thf('46', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['44', '45'])).
% 0.83/1.06  thf('47', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0)
% 0.83/1.06          | ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.83/1.06      inference('simplify', [status(thm)], ['46'])).
% 0.83/1.06  thf('48', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['40', '47'])).
% 0.83/1.06  thf('49', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['37', '48'])).
% 0.83/1.06  thf('50', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['36', '49'])).
% 0.83/1.06  thf(t54_relat_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( v1_relat_1 @ A ) =>
% 0.83/1.06       ( ![B:$i]:
% 0.83/1.06         ( ( v1_relat_1 @ B ) =>
% 0.83/1.06           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.83/1.06             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.83/1.06  thf('51', plain,
% 0.83/1.06      (![X23 : $i, X24 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X23)
% 0.83/1.06          | ((k4_relat_1 @ (k5_relat_1 @ X24 @ X23))
% 0.83/1.06              = (k5_relat_1 @ (k4_relat_1 @ X23) @ (k4_relat_1 @ X24)))
% 0.83/1.06          | ~ (v1_relat_1 @ X24))),
% 0.83/1.06      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.83/1.06  thf('52', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.06            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['50', '51'])).
% 0.83/1.06  thf(t62_relat_1, conjecture,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( v1_relat_1 @ A ) =>
% 0.83/1.06       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.83/1.06         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.83/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.06    (~( ![A:$i]:
% 0.83/1.06        ( ( v1_relat_1 @ A ) =>
% 0.83/1.06          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.83/1.06            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.83/1.06    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.83/1.06  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('54', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.83/1.06  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('56', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.83/1.06      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.83/1.06  thf('57', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.83/1.06          | ~ (v1_xboole_0 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ X1))),
% 0.83/1.06      inference('sup+', [status(thm)], ['2', '25'])).
% 0.83/1.06  thf('58', plain,
% 0.83/1.06      (![X15 : $i, X16 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X15)
% 0.83/1.06          | ~ (v1_relat_1 @ X16)
% 0.83/1.06          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.83/1.06      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.83/1.06  thf('59', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         ((v1_relat_1 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_xboole_0 @ X1)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ X1))),
% 0.83/1.06      inference('sup+', [status(thm)], ['57', '58'])).
% 0.83/1.06  thf('60', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X1)
% 0.83/1.06          | ~ (v1_xboole_0 @ X1)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | (v1_relat_1 @ k1_xboole_0))),
% 0.83/1.06      inference('simplify', [status(thm)], ['59'])).
% 0.83/1.06  thf('61', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (~ (v1_xboole_0 @ X0)
% 0.83/1.06          | (v1_relat_1 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_relat_1 @ X1)
% 0.83/1.06          | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['56', '60'])).
% 0.83/1.06  thf('62', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X1)
% 0.83/1.06          | (v1_relat_1 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('simplify', [status(thm)], ['61'])).
% 0.83/1.06  thf('63', plain,
% 0.83/1.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['55', '62'])).
% 0.83/1.06  thf('64', plain,
% 0.83/1.06      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['54', '63'])).
% 0.83/1.06  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.83/1.06      inference('sup-', [status(thm)], ['53', '64'])).
% 0.83/1.06  thf('66', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.06            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('demod', [status(thm)], ['52', '65'])).
% 0.83/1.06  thf('67', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.83/1.06          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('sup+', [status(thm)], ['27', '66'])).
% 0.83/1.06  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.06  thf('69', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('demod', [status(thm)], ['67', '68'])).
% 0.83/1.06  thf('70', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0)
% 0.83/1.06          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.83/1.06      inference('simplify', [status(thm)], ['69'])).
% 0.83/1.06  thf(involutiveness_k4_relat_1, axiom,
% 0.83/1.06    (![A:$i]:
% 0.83/1.06     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.83/1.06  thf('71', plain,
% 0.83/1.06      (![X18 : $i]:
% 0.83/1.06         (((k4_relat_1 @ (k4_relat_1 @ X18)) = (X18)) | ~ (v1_relat_1 @ X18))),
% 0.83/1.06      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.83/1.06  thf('72', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.06      inference('sup+', [status(thm)], ['70', '71'])).
% 0.83/1.06  thf('73', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.83/1.06      inference('sup-', [status(thm)], ['36', '49'])).
% 0.83/1.06  thf('74', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['72', '73'])).
% 0.83/1.06  thf('75', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ k1_xboole_0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.06      inference('sup-', [status(thm)], ['0', '74'])).
% 0.83/1.06  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.83/1.06      inference('sup-', [status(thm)], ['53', '64'])).
% 0.83/1.06  thf('77', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0)
% 0.83/1.06          | ~ (v1_relat_1 @ X0)
% 0.83/1.06          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['75', '76'])).
% 0.83/1.06  thf('78', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.83/1.06          | ~ (v1_relat_1 @ X0))),
% 0.83/1.06      inference('simplify', [status(thm)], ['77'])).
% 0.83/1.06  thf('79', plain,
% 0.83/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf('80', plain,
% 0.83/1.06      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.83/1.06        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.83/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.06  thf('81', plain,
% 0.83/1.06      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.83/1.06         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.83/1.06      inference('split', [status(esa)], ['80'])).
% 0.83/1.06  thf('82', plain,
% 0.83/1.06      ((![X0 : $i]:
% 0.83/1.06          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.83/1.06         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.83/1.06      inference('sup-', [status(thm)], ['79', '81'])).
% 0.83/1.06  thf('83', plain,
% 0.83/1.06      (![X0 : $i]:
% 0.83/1.06         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.83/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.83/1.06  thf('84', plain,
% 0.83/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf('85', plain,
% 0.83/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.06      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.06  thf('86', plain,
% 0.83/1.06      (![X0 : $i, X1 : $i]:
% 0.83/1.06         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.83/1.07      inference('sup+', [status(thm)], ['84', '85'])).
% 0.83/1.07  thf('87', plain,
% 0.83/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.83/1.07  thf('88', plain,
% 0.83/1.07      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.83/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.83/1.07      inference('split', [status(esa)], ['80'])).
% 0.83/1.07  thf('89', plain,
% 0.83/1.07      ((![X0 : $i]:
% 0.83/1.07          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.83/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['87', '88'])).
% 0.83/1.07  thf('90', plain,
% 0.83/1.07      ((![X0 : $i, X1 : $i]:
% 0.83/1.07          (((X0) != (k1_xboole_0))
% 0.83/1.07           | ~ (v1_xboole_0 @ X0)
% 0.83/1.07           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.83/1.07           | ~ (v1_xboole_0 @ X1)))
% 0.83/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['86', '89'])).
% 0.83/1.07  thf('91', plain,
% 0.83/1.07      ((![X1 : $i]:
% 0.83/1.07          (~ (v1_xboole_0 @ X1)
% 0.83/1.07           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.83/1.07           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.83/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['90'])).
% 0.83/1.07  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf('93', plain,
% 0.83/1.07      ((![X1 : $i]:
% 0.83/1.07          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.83/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.83/1.07      inference('simplify_reflect+', [status(thm)], ['91', '92'])).
% 0.83/1.07  thf('94', plain,
% 0.83/1.07      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.83/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['83', '93'])).
% 0.83/1.07  thf('95', plain, ((v1_relat_1 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf('97', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.83/1.07      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.83/1.07  thf('98', plain,
% 0.83/1.07      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.83/1.07       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.83/1.07      inference('split', [status(esa)], ['80'])).
% 0.83/1.07  thf('99', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.83/1.07      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 0.83/1.07  thf('100', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.83/1.07      inference('simpl_trail', [status(thm)], ['82', '99'])).
% 0.83/1.07  thf('101', plain,
% 0.83/1.07      ((((k1_xboole_0) != (k1_xboole_0))
% 0.83/1.07        | ~ (v1_relat_1 @ sk_A)
% 0.83/1.07        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['78', '100'])).
% 0.83/1.07  thf('102', plain, ((v1_relat_1 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.07  thf('104', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.83/1.07      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.83/1.07  thf('105', plain, ($false), inference('simplify', [status(thm)], ['104'])).
% 0.83/1.07  
% 0.83/1.07  % SZS output end Refutation
% 0.83/1.07  
% 0.83/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
