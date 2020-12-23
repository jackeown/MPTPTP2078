%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JCDah395vE

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:46 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 804 expanded)
%              Number of leaves         :   26 ( 251 expanded)
%              Depth                    :   28
%              Number of atoms          :  912 (6239 expanded)
%              Number of equality atoms :   83 ( 504 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( m1_subset_1 @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ( m1_subset_1 @ X25 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('40',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ( m1_subset_1 @ X25 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('45',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','27'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ( m1_subset_1 @ X25 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('56',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['30','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','27'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['3','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','67'])).

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

thf('69',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('73',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['69','74'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('86',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    r1_xboole_0 @ sk_B @ sk_B ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','98'])).

thf('100',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('102',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JCDah395vE
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.37/1.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.56  % Solved by: fo/fo7.sh
% 1.37/1.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.56  % done 2460 iterations in 1.092s
% 1.37/1.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.56  % SZS output start Refutation
% 1.37/1.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.37/1.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.37/1.56  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.37/1.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.37/1.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.37/1.56  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.37/1.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.56  thf(t3_boole, axiom,
% 1.37/1.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.37/1.56  thf('0', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.37/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.56  thf(t48_xboole_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]:
% 1.37/1.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.37/1.56  thf('1', plain,
% 1.37/1.56      (![X7 : $i, X8 : $i]:
% 1.37/1.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 1.37/1.56           = (k3_xboole_0 @ X7 @ X8))),
% 1.37/1.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.37/1.56  thf('2', plain,
% 1.37/1.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.56      inference('sup+', [status(thm)], ['0', '1'])).
% 1.37/1.56  thf('3', plain,
% 1.37/1.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.56      inference('sup+', [status(thm)], ['0', '1'])).
% 1.37/1.56  thf('4', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.37/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.37/1.56  thf('5', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.37/1.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.37/1.56  thf(d1_zfmisc_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]:
% 1.37/1.56     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.37/1.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.37/1.56  thf('6', plain,
% 1.37/1.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.37/1.56         (~ (r1_tarski @ X18 @ X19)
% 1.37/1.56          | (r2_hidden @ X18 @ X20)
% 1.37/1.56          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 1.37/1.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.37/1.56  thf('7', plain,
% 1.37/1.56      (![X18 : $i, X19 : $i]:
% 1.37/1.56         ((r2_hidden @ X18 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X18 @ X19))),
% 1.37/1.56      inference('simplify', [status(thm)], ['6'])).
% 1.37/1.56  thf('8', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.37/1.56      inference('sup-', [status(thm)], ['5', '7'])).
% 1.37/1.56  thf(d2_subset_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]:
% 1.37/1.56     ( ( ( v1_xboole_0 @ A ) =>
% 1.37/1.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.37/1.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.37/1.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.37/1.56  thf('9', plain,
% 1.37/1.56      (![X23 : $i, X24 : $i]:
% 1.37/1.56         (~ (r2_hidden @ X23 @ X24)
% 1.37/1.56          | (m1_subset_1 @ X23 @ X24)
% 1.37/1.56          | (v1_xboole_0 @ X24))),
% 1.37/1.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.37/1.56  thf('10', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['8', '9'])).
% 1.37/1.56  thf(d5_subset_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]:
% 1.37/1.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.37/1.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.37/1.56  thf('11', plain,
% 1.37/1.56      (![X26 : $i, X27 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.37/1.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.37/1.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.56  thf('12', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ k1_xboole_0)
% 1.37/1.56              = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['10', '11'])).
% 1.37/1.56  thf('13', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.37/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.56  thf('14', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.37/1.56      inference('demod', [status(thm)], ['12', '13'])).
% 1.37/1.56  thf('15', plain,
% 1.37/1.56      (![X24 : $i, X25 : $i]:
% 1.37/1.56         (~ (v1_xboole_0 @ X25)
% 1.37/1.56          | (m1_subset_1 @ X25 @ X24)
% 1.37/1.56          | ~ (v1_xboole_0 @ X24))),
% 1.37/1.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.37/1.56  thf('16', plain,
% 1.37/1.56      (![X26 : $i, X27 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.37/1.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.37/1.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.56  thf('17', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ~ (v1_xboole_0 @ X1)
% 1.37/1.56          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['15', '16'])).
% 1.37/1.56  thf('18', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 1.37/1.56          | ~ (v1_xboole_0 @ X1))),
% 1.37/1.56      inference('sup-', [status(thm)], ['14', '17'])).
% 1.37/1.56  thf('19', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.37/1.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.37/1.56          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.37/1.56      inference('sup+', [status(thm)], ['4', '18'])).
% 1.37/1.56  thf('20', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.37/1.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.37/1.56  thf('21', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.37/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.56  thf(t83_xboole_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]:
% 1.37/1.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.37/1.56  thf('22', plain,
% 1.37/1.56      (![X12 : $i, X14 : $i]:
% 1.37/1.56         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 1.37/1.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.37/1.56  thf('23', plain,
% 1.37/1.56      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.56      inference('sup-', [status(thm)], ['21', '22'])).
% 1.37/1.56  thf('24', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.37/1.56      inference('simplify', [status(thm)], ['23'])).
% 1.37/1.56  thf(t68_xboole_1, axiom,
% 1.37/1.56    (![A:$i,B:$i,C:$i]:
% 1.37/1.56     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.37/1.56       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 1.37/1.56            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 1.37/1.56  thf('25', plain,
% 1.37/1.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.37/1.56         (~ (r1_xboole_0 @ X9 @ X10)
% 1.37/1.56          | (v1_xboole_0 @ X11)
% 1.37/1.56          | ~ (r1_tarski @ X11 @ X9)
% 1.37/1.56          | ~ (r1_tarski @ X11 @ X10))),
% 1.37/1.56      inference('cnf', [status(esa)], [t68_xboole_1])).
% 1.37/1.56  thf('26', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 1.37/1.56          | ~ (r1_tarski @ X1 @ X0)
% 1.37/1.56          | (v1_xboole_0 @ X1))),
% 1.37/1.56      inference('sup-', [status(thm)], ['24', '25'])).
% 1.37/1.56  thf('27', plain,
% 1.37/1.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 1.37/1.56      inference('condensation', [status(thm)], ['26'])).
% 1.37/1.56  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.37/1.56      inference('sup-', [status(thm)], ['20', '27'])).
% 1.37/1.56  thf('29', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.37/1.56      inference('demod', [status(thm)], ['19', '28'])).
% 1.37/1.56  thf('30', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.37/1.56      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.56  thf('31', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['8', '9'])).
% 1.37/1.56  thf(dt_k3_subset_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]:
% 1.37/1.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.37/1.56       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.37/1.56  thf('32', plain,
% 1.37/1.56      (![X28 : $i, X29 : $i]:
% 1.37/1.56         ((m1_subset_1 @ (k3_subset_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 1.37/1.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 1.37/1.56      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.37/1.56  thf('33', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 1.37/1.56             (k1_zfmisc_1 @ X0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['31', '32'])).
% 1.37/1.56  thf('34', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.37/1.56      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.56  thf('35', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 1.37/1.56      inference('demod', [status(thm)], ['33', '34'])).
% 1.37/1.56  thf('36', plain,
% 1.37/1.56      (![X26 : $i, X27 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.37/1.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.37/1.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.56  thf('37', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['35', '36'])).
% 1.37/1.56  thf('38', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.37/1.56      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.56  thf('39', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['8', '9'])).
% 1.37/1.56  thf(involutiveness_k3_subset_1, axiom,
% 1.37/1.56    (![A:$i,B:$i]:
% 1.37/1.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.37/1.56       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.37/1.56  thf('40', plain,
% 1.37/1.56      (![X30 : $i, X31 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 1.37/1.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 1.37/1.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.37/1.56  thf('41', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 1.37/1.56              = (k1_xboole_0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['39', '40'])).
% 1.37/1.56  thf('42', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.37/1.56      inference('simplify', [status(thm)], ['29'])).
% 1.37/1.56  thf('43', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.37/1.56      inference('demod', [status(thm)], ['41', '42'])).
% 1.37/1.56  thf('44', plain,
% 1.37/1.56      (![X24 : $i, X25 : $i]:
% 1.37/1.56         (~ (v1_xboole_0 @ X25)
% 1.37/1.56          | (m1_subset_1 @ X25 @ X24)
% 1.37/1.56          | ~ (v1_xboole_0 @ X24))),
% 1.37/1.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.37/1.56  thf('45', plain,
% 1.37/1.56      (![X30 : $i, X31 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 1.37/1.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 1.37/1.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.37/1.56  thf('46', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ~ (v1_xboole_0 @ X1)
% 1.37/1.56          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['44', '45'])).
% 1.37/1.56  thf('47', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1))
% 1.37/1.56          | ~ (v1_xboole_0 @ X1))),
% 1.37/1.56      inference('sup-', [status(thm)], ['43', '46'])).
% 1.37/1.56  thf('48', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.37/1.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.37/1.56          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.37/1.56      inference('sup+', [status(thm)], ['38', '47'])).
% 1.37/1.56  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.37/1.56      inference('sup-', [status(thm)], ['20', '27'])).
% 1.37/1.56  thf('50', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.37/1.56      inference('demod', [status(thm)], ['48', '49'])).
% 1.37/1.56  thf('51', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.56      inference('simplify', [status(thm)], ['50'])).
% 1.37/1.56  thf('52', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.37/1.56      inference('demod', [status(thm)], ['37', '51'])).
% 1.37/1.56  thf('53', plain,
% 1.37/1.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.56      inference('sup+', [status(thm)], ['0', '1'])).
% 1.37/1.56  thf('54', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.37/1.56          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.37/1.56      inference('sup+', [status(thm)], ['52', '53'])).
% 1.37/1.56  thf('55', plain,
% 1.37/1.56      (![X24 : $i, X25 : $i]:
% 1.37/1.56         (~ (v1_xboole_0 @ X25)
% 1.37/1.56          | (m1_subset_1 @ X25 @ X24)
% 1.37/1.56          | ~ (v1_xboole_0 @ X24))),
% 1.37/1.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.37/1.56  thf('56', plain,
% 1.37/1.56      (![X28 : $i, X29 : $i]:
% 1.37/1.56         ((m1_subset_1 @ (k3_subset_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 1.37/1.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 1.37/1.56      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.37/1.56  thf('57', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ~ (v1_xboole_0 @ X1)
% 1.37/1.56          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['55', '56'])).
% 1.37/1.56  thf('58', plain,
% 1.37/1.56      (![X0 : $i, X1 : $i]:
% 1.37/1.56         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.37/1.56          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ~ (v1_xboole_0 @ X1))),
% 1.37/1.56      inference('sup-', [status(thm)], ['54', '57'])).
% 1.37/1.56  thf('59', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.37/1.56          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.37/1.56      inference('sup+', [status(thm)], ['30', '58'])).
% 1.37/1.56  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.37/1.56      inference('sup-', [status(thm)], ['20', '27'])).
% 1.37/1.56  thf('61', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 1.37/1.56          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.37/1.56      inference('demod', [status(thm)], ['59', '60'])).
% 1.37/1.56  thf('62', plain,
% 1.37/1.56      (![X26 : $i, X27 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.37/1.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.37/1.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.56  thf('63', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.37/1.56          | ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.37/1.56      inference('sup-', [status(thm)], ['61', '62'])).
% 1.37/1.56  thf('64', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.56      inference('simplify', [status(thm)], ['50'])).
% 1.37/1.56  thf('65', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.37/1.56          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.37/1.56      inference('demod', [status(thm)], ['63', '64'])).
% 1.37/1.56  thf('66', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.37/1.56          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.37/1.56      inference('sup+', [status(thm)], ['3', '65'])).
% 1.37/1.56  thf('67', plain,
% 1.37/1.56      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.56      inference('simplify', [status(thm)], ['66'])).
% 1.37/1.56  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.56      inference('demod', [status(thm)], ['2', '67'])).
% 1.37/1.56  thf(t40_subset_1, conjecture,
% 1.37/1.56    (![A:$i,B:$i,C:$i]:
% 1.37/1.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.37/1.56       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 1.37/1.56         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.37/1.56  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.56    (~( ![A:$i,B:$i,C:$i]:
% 1.37/1.56        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.37/1.56          ( ( ( r1_tarski @ B @ C ) & 
% 1.37/1.56              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 1.37/1.56            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 1.37/1.56    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 1.37/1.56  thf('69', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('70', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('71', plain,
% 1.37/1.56      (![X26 : $i, X27 : $i]:
% 1.37/1.56         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.37/1.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.37/1.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.37/1.56  thf('72', plain,
% 1.37/1.56      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.37/1.56      inference('sup-', [status(thm)], ['70', '71'])).
% 1.37/1.56  thf(t106_xboole_1, axiom,
% 1.37/1.56    (![A:$i,B:$i,C:$i]:
% 1.37/1.56     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.37/1.56       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.37/1.56  thf('73', plain,
% 1.37/1.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.37/1.56         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.37/1.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.37/1.56  thf('74', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 1.37/1.56          | (r1_tarski @ X0 @ sk_A))),
% 1.37/1.56      inference('sup-', [status(thm)], ['72', '73'])).
% 1.37/1.56  thf('75', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.37/1.56      inference('sup-', [status(thm)], ['69', '74'])).
% 1.37/1.56  thf(t85_xboole_1, axiom,
% 1.37/1.56    (![A:$i,B:$i,C:$i]:
% 1.37/1.56     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.37/1.56  thf('76', plain,
% 1.37/1.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.37/1.56         (~ (r1_tarski @ X15 @ X16)
% 1.37/1.56          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 1.37/1.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.37/1.56  thf('77', plain,
% 1.37/1.56      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))),
% 1.37/1.56      inference('sup-', [status(thm)], ['75', '76'])).
% 1.37/1.56  thf('78', plain,
% 1.37/1.56      (![X12 : $i, X13 : $i]:
% 1.37/1.56         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.37/1.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.37/1.56  thf('79', plain,
% 1.37/1.56      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)) = (sk_B))),
% 1.37/1.56      inference('sup-', [status(thm)], ['77', '78'])).
% 1.37/1.56  thf('80', plain,
% 1.37/1.56      (![X7 : $i, X8 : $i]:
% 1.37/1.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 1.37/1.56           = (k3_xboole_0 @ X7 @ X8))),
% 1.37/1.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.37/1.56  thf('81', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((k4_xboole_0 @ sk_B @ sk_B)
% 1.37/1.56           = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 1.37/1.56      inference('sup+', [status(thm)], ['79', '80'])).
% 1.37/1.56  thf('82', plain,
% 1.37/1.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.56      inference('sup+', [status(thm)], ['0', '1'])).
% 1.37/1.56  thf('83', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         ((k3_xboole_0 @ sk_B @ k1_xboole_0)
% 1.37/1.56           = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 1.37/1.56      inference('demod', [status(thm)], ['81', '82'])).
% 1.37/1.56  thf('84', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('85', plain,
% 1.37/1.56      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.37/1.56      inference('sup-', [status(thm)], ['70', '71'])).
% 1.37/1.56  thf('86', plain,
% 1.37/1.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.37/1.56         ((r1_xboole_0 @ X2 @ X4)
% 1.37/1.56          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.37/1.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.37/1.56  thf('87', plain,
% 1.37/1.56      (![X0 : $i]:
% 1.37/1.56         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 1.37/1.56          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 1.37/1.56      inference('sup-', [status(thm)], ['85', '86'])).
% 1.37/1.56  thf('88', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.37/1.56      inference('sup-', [status(thm)], ['84', '87'])).
% 1.37/1.56  thf('89', plain,
% 1.37/1.56      (![X12 : $i, X13 : $i]:
% 1.37/1.56         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.37/1.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.37/1.56  thf('90', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 1.37/1.56      inference('sup-', [status(thm)], ['88', '89'])).
% 1.37/1.56  thf('91', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('92', plain,
% 1.37/1.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.37/1.56         (~ (r1_tarski @ X15 @ X16)
% 1.37/1.56          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 1.37/1.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.37/1.56  thf('93', plain,
% 1.37/1.56      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 1.37/1.56      inference('sup-', [status(thm)], ['91', '92'])).
% 1.37/1.56  thf('94', plain, ((r1_xboole_0 @ sk_B @ sk_B)),
% 1.37/1.56      inference('sup+', [status(thm)], ['90', '93'])).
% 1.37/1.56  thf('95', plain,
% 1.37/1.56      (![X12 : $i, X13 : $i]:
% 1.37/1.56         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.37/1.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.37/1.56  thf('96', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 1.37/1.56      inference('sup-', [status(thm)], ['94', '95'])).
% 1.37/1.56  thf('97', plain,
% 1.37/1.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.56      inference('sup+', [status(thm)], ['0', '1'])).
% 1.37/1.56  thf('98', plain, (((k3_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))),
% 1.37/1.56      inference('demod', [status(thm)], ['96', '97'])).
% 1.37/1.56  thf('99', plain,
% 1.37/1.56      (![X0 : $i]: ((sk_B) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 1.37/1.56      inference('demod', [status(thm)], ['83', '98'])).
% 1.37/1.56  thf('100', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 1.37/1.56      inference('sup+', [status(thm)], ['68', '99'])).
% 1.37/1.56  thf('101', plain,
% 1.37/1.56      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.56      inference('simplify', [status(thm)], ['66'])).
% 1.37/1.56  thf('102', plain, (((sk_B) = (k1_xboole_0))),
% 1.37/1.56      inference('demod', [status(thm)], ['100', '101'])).
% 1.37/1.56  thf('103', plain, (((sk_B) != (k1_xboole_0))),
% 1.37/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.56  thf('104', plain, ($false),
% 1.37/1.56      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 1.37/1.56  
% 1.37/1.56  % SZS output end Refutation
% 1.37/1.56  
% 1.39/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
