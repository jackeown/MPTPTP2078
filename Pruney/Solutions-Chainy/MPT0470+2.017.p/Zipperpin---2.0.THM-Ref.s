%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XnNuQa3j5e

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 459 expanded)
%              Number of leaves         :   33 ( 159 expanded)
%              Depth                    :   26
%              Number of atoms          :  816 (3391 expanded)
%              Number of equality atoms :   88 ( 392 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_relat_1 @ X47 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_relat_1 @ X47 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X53 @ X52 ) ) @ ( k1_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

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

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X51 @ X50 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X51 ) @ ( k4_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = ( k5_xboole_0 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X45: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8','29'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('31',plain,(
    ! [X49: $i] :
      ( ( ( k3_xboole_0 @ X49 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) )
        = X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X36 @ X38 ) @ X37 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('36',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k6_subset_1 @ X36 @ X38 ) @ X37 )
      = ( k6_subset_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k6_subset_1 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','45'])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','28'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','53'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X55 @ X54 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X54 ) @ ( k4_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','28'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X45: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('62',plain,(
    ! [X48: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X48 ) )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','53'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','28'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('73',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('74',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('79',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['71','79'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(simplify,[status(thm)],['83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XnNuQa3j5e
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 209 iterations in 0.096s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(dt_k5_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.55       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X46 : $i, X47 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X46)
% 0.20/0.55          | ~ (v1_relat_1 @ X47)
% 0.20/0.55          | (v1_relat_1 @ (k5_relat_1 @ X46 @ X47)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X46 : $i, X47 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X46)
% 0.20/0.55          | ~ (v1_relat_1 @ X47)
% 0.20/0.55          | (v1_relat_1 @ (k5_relat_1 @ X46 @ X47)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.55  thf(t60_relat_1, axiom,
% 0.20/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('2', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.55  thf(t44_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v1_relat_1 @ B ) =>
% 0.20/0.55           ( r1_tarski @
% 0.20/0.55             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X52 : $i, X53 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X52)
% 0.20/0.55          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X53 @ X52)) @ 
% 0.20/0.55             (k1_relat_1 @ X53))
% 0.20/0.55          | ~ (v1_relat_1 @ X53))),
% 0.20/0.55      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i]:
% 0.20/0.55         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.20/0.55               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.20/0.55          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_tarski @ k1_xboole_0 @ 
% 0.20/0.55             (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 0.20/0.55          | ((k1_relat_1 @ k1_xboole_0)
% 0.20/0.55              = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('7', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.55  thf(t62_relat_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.55         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( v1_relat_1 @ A ) =>
% 0.20/0.55          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.55            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.20/0.55  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc1_relat_1, axiom,
% 0.20/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.55  thf('10', plain, (![X44 : $i]: ((v1_relat_1 @ X44) | ~ (v1_xboole_0 @ X44))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.55  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.55  thf(t100_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.20/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X40 : $i, X41 : $i]:
% 0.20/0.55         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i]:
% 0.20/0.55         ((k6_subset_1 @ X4 @ X5)
% 0.20/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf(t41_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v1_relat_1 @ B ) =>
% 0.20/0.55           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.20/0.55             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X50 : $i, X51 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X50)
% 0.20/0.55          | ((k4_relat_1 @ (k6_subset_1 @ X51 @ X50))
% 0.20/0.55              = (k6_subset_1 @ (k4_relat_1 @ X51) @ (k4_relat_1 @ X50)))
% 0.20/0.55          | ~ (v1_relat_1 @ X51))),
% 0.20/0.55      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_relat_1 @ (k6_subset_1 @ X0 @ X0))
% 0.20/0.55            = (k5_xboole_0 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf(t92_xboole_1, axiom,
% 0.20/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('19', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k4_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.55  thf(dt_k4_relat_1, axiom,
% 0.20/0.55    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X45 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X45)) | ~ (v1_relat_1 @ X45))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_relat_1 @ k1_xboole_0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '23'])).
% 0.20/0.55  thf('25', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.55  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf('27', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['24', '27'])).
% 0.20/0.55  thf('29', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['6', '7', '8', '29'])).
% 0.20/0.55  thf(t22_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ( k3_xboole_0 @
% 0.20/0.55           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.20/0.55         ( A ) ) ))).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X49 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X49 @ 
% 0.20/0.55            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))) = (
% 0.20/0.55            X49))
% 0.20/0.55          | ~ (v1_relat_1 @ X49))),
% 0.20/0.55      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.55            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.20/0.55             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.20/0.55            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.55  thf('33', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf(t125_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.20/0.55         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.20/0.55       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.55         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.55         ((k2_zfmisc_1 @ (k4_xboole_0 @ X36 @ X38) @ X37)
% 0.20/0.55           = (k4_xboole_0 @ (k2_zfmisc_1 @ X36 @ X37) @ 
% 0.20/0.55              (k2_zfmisc_1 @ X38 @ X37)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X40 : $i, X41 : $i]:
% 0.20/0.55         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X40 : $i, X41 : $i]:
% 0.20/0.55         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.55         ((k2_zfmisc_1 @ (k6_subset_1 @ X36 @ X38) @ X37)
% 0.20/0.55           = (k6_subset_1 @ (k2_zfmisc_1 @ X36 @ X37) @ 
% 0.20/0.55              (k2_zfmisc_1 @ X38 @ X37)))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k2_zfmisc_1 @ (k6_subset_1 @ X1 @ X1) @ X0)
% 0.20/0.55           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['34', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('41', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['33', '42'])).
% 0.20/0.55  thf(t2_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '43', '44'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '45'])).
% 0.20/0.55  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '28'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.55  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('51', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ X8) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k4_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.55  thf('54', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.55  thf(t54_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v1_relat_1 @ B ) =>
% 0.20/0.55           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.55             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X54 : $i, X55 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X54)
% 0.20/0.55          | ((k4_relat_1 @ (k5_relat_1 @ X55 @ X54))
% 0.20/0.55              = (k5_relat_1 @ (k4_relat_1 @ X54) @ (k4_relat_1 @ X55)))
% 0.20/0.55          | ~ (v1_relat_1 @ X55))),
% 0.20/0.55      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.55            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.55  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '28'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.55            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['49', '58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X45 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X45)) | ~ (v1_relat_1 @ X45))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.20/0.55      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf(involutiveness_k4_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X48 : $i]:
% 0.20/0.55         (((k4_relat_1 @ (k4_relat_1 @ X48)) = (X48)) | ~ (v1_relat_1 @ X48))),
% 0.20/0.55      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.20/0.55  thf('64', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '65'])).
% 0.20/0.55  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '28'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.20/0.55        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['70'])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['70'])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.55  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.55      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.55  thf('77', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.55       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('split', [status(esa)], ['70'])).
% 0.20/0.55  thf('79', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.20/0.55  thf('80', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['71', '79'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['69', '80'])).
% 0.20/0.55  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('83', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['81', '82'])).
% 0.20/0.55  thf('84', plain, ($false), inference('simplify', [status(thm)], ['83'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
