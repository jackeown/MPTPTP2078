%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NCpJlpxsL7

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:37 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 451 expanded)
%              Number of leaves         :   32 ( 157 expanded)
%              Depth                    :   23
%              Number of atoms          :  928 (3341 expanded)
%              Number of equality atoms :  102 ( 400 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

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

thf('1',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X48 @ X47 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X48 ) @ ( k4_relat_1 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = ( k5_xboole_0 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','14'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X52 @ X51 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X51 ) @ ( k4_relat_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('37',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X49 @ X50 ) )
        = ( k2_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X49 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','46'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('48',plain,(
    ! [X46: $i] :
      ( ( ( k3_xboole_0 @ X46 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ ( k2_relat_1 @ X46 ) ) )
        = X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('51',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ X36 @ ( k4_xboole_0 @ X33 @ X35 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X36 @ X33 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('52',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('53',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ X36 @ ( k6_subset_1 @ X33 @ X35 ) )
      = ( k6_subset_1 @ ( k2_zfmisc_1 @ X36 @ X33 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('58',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['49','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_subset_1 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('65',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['63','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','68'])).

thf('70',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','27'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','72'])).

thf('74',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('76',plain,(
    ! [X45: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X45 ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','14'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','79'])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','27'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('87',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['84'])).

thf('88',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['84'])).

thf('93',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['85','93'])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(simplify,[status(thm)],['97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NCpJlpxsL7
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 16:59:06 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 291 iterations in 0.121s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.40/0.60  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(dt_k5_relat_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.40/0.60       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (![X43 : $i, X44 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X43)
% 0.40/0.60          | ~ (v1_relat_1 @ X44)
% 0.40/0.60          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.60  thf(t62_relat_1, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.40/0.60         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( v1_relat_1 @ A ) =>
% 0.40/0.60          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.40/0.60            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.40/0.60  thf('1', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t92_xboole_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('2', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf(t41_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( v1_relat_1 @ B ) =>
% 0.40/0.60           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.40/0.60             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X47 : $i, X48 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X47)
% 0.40/0.60          | ((k4_relat_1 @ (k6_subset_1 @ X48 @ X47))
% 0.40/0.60              = (k6_subset_1 @ (k4_relat_1 @ X48) @ (k4_relat_1 @ X47)))
% 0.40/0.60          | ~ (v1_relat_1 @ X48))),
% 0.40/0.60      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.40/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.60  thf('4', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.60  thf(t100_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X1 @ X2)
% 0.40/0.60           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.60  thf(redefinition_k6_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X37 : $i, X38 : $i]:
% 0.40/0.60         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i]:
% 0.40/0.60         ((k6_subset_1 @ X1 @ X2)
% 0.40/0.60           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['4', '7'])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k4_relat_1 @ (k6_subset_1 @ X0 @ X0))
% 0.40/0.60            = (k5_xboole_0 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ X0)))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['3', '8'])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['4', '7'])).
% 0.40/0.60  thf('11', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k4_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k4_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['2', '13'])).
% 0.40/0.60  thf('15', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '14'])).
% 0.40/0.60  thf(t54_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( v1_relat_1 @ B ) =>
% 0.40/0.60           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.40/0.60             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X51 : $i, X52 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X51)
% 0.40/0.60          | ((k4_relat_1 @ (k5_relat_1 @ X52 @ X51))
% 0.40/0.60              = (k5_relat_1 @ (k4_relat_1 @ X51) @ (k4_relat_1 @ X52)))
% 0.40/0.60          | ~ (v1_relat_1 @ X52))),
% 0.40/0.60      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.60            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.40/0.60  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(cc1_relat_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.40/0.60  thf('19', plain, (![X41 : $i]: ((v1_relat_1 @ X41) | ~ (v1_xboole_0 @ X41))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k4_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.60  thf(dt_k4_relat_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X42 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X42)) | ~ (v1_relat_1 @ X42))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['20', '21'])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['19', '22'])).
% 0.40/0.60  thf('24', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.60  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.60  thf('26', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.60      inference('demod', [status(thm)], ['23', '26'])).
% 0.40/0.60  thf('28', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['18', '27'])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.60            = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '28'])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X43 : $i, X44 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X43)
% 0.40/0.60          | ~ (v1_relat_1 @ X44)
% 0.40/0.60          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.60  thf('31', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf(t2_boole, axiom,
% 0.40/0.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X1 : $i, X2 : $i]:
% 0.40/0.60         ((k6_subset_1 @ X1 @ X2)
% 0.40/0.60           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k6_subset_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.40/0.60           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.40/0.60  thf('36', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf('37', plain, (![X41 : $i]: ((v1_relat_1 @ X41) | ~ (v1_xboole_0 @ X41))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.60  thf(t60_relat_1, axiom,
% 0.40/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf(t47_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( v1_relat_1 @ B ) =>
% 0.40/0.60           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.40/0.60             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X49 : $i, X50 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X49)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X49 @ X50)) = (k2_relat_1 @ X50))
% 0.40/0.60          | ~ (r1_tarski @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X49))
% 0.40/0.60          | ~ (v1_relat_1 @ X50))),
% 0.40/0.60      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.60              = (k2_relat_1 @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.60  thf('41', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.40/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.60  thf('42', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['37', '43'])).
% 0.40/0.60  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['44', '45'])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k2_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.40/0.60            = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['36', '46'])).
% 0.40/0.60  thf(t22_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ( k3_xboole_0 @
% 0.40/0.60           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.40/0.60         ( A ) ) ))).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      (![X46 : $i]:
% 0.40/0.60         (((k3_xboole_0 @ X46 @ 
% 0.40/0.60            (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ (k2_relat_1 @ X46))) = (
% 0.40/0.60            X46))
% 0.40/0.60          | ~ (v1_relat_1 @ X46))),
% 0.40/0.60      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k3_xboole_0 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 0.40/0.60            (k2_zfmisc_1 @ 
% 0.40/0.60             (k1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))) @ 
% 0.40/0.60             k1_xboole_0))
% 0.40/0.60            = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.40/0.60  thf('50', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf(t125_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.40/0.60         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.40/0.60       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.60         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      (![X33 : $i, X35 : $i, X36 : $i]:
% 0.40/0.60         ((k2_zfmisc_1 @ X36 @ (k4_xboole_0 @ X33 @ X35))
% 0.40/0.60           = (k4_xboole_0 @ (k2_zfmisc_1 @ X36 @ X33) @ 
% 0.40/0.60              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      (![X37 : $i, X38 : $i]:
% 0.40/0.60         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.60  thf('53', plain,
% 0.40/0.60      (![X37 : $i, X38 : $i]:
% 0.40/0.60         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      (![X33 : $i, X35 : $i, X36 : $i]:
% 0.40/0.60         ((k2_zfmisc_1 @ X36 @ (k6_subset_1 @ X33 @ X35))
% 0.40/0.60           = (k6_subset_1 @ (k2_zfmisc_1 @ X36 @ X33) @ 
% 0.40/0.60              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.40/0.60      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['4', '7'])).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k2_zfmisc_1 @ X1 @ (k6_subset_1 @ X0 @ X0))
% 0.40/0.60           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['54', '55'])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['4', '7'])).
% 0.40/0.60  thf('58', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.40/0.60      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['50', '59'])).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k1_xboole_0) = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['49', '60', '61'])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ 
% 0.40/0.60             (k5_relat_1 @ X1 @ 
% 0.40/0.60              (k6_subset_1 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ((k1_xboole_0)
% 0.40/0.60              = (k5_relat_1 @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['35', '62'])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k6_subset_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.40/0.60           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.40/0.60  thf('65', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k6_subset_1 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['64', '65'])).
% 0.40/0.60  thf('67', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      (![X1 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X1)
% 0.40/0.60          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['63', '66', '67'])).
% 0.40/0.60  thf('69', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['30', '68'])).
% 0.40/0.60  thf('70', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['18', '27'])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['69', '70'])).
% 0.40/0.60  thf('72', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['71'])).
% 0.40/0.60  thf('73', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['29', '72'])).
% 0.40/0.60  thf('74', plain,
% 0.40/0.60      (![X42 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X42)) | ~ (v1_relat_1 @ X42))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.40/0.60  thf('75', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k1_xboole_0) = (k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.40/0.60      inference('clc', [status(thm)], ['73', '74'])).
% 0.40/0.60  thf(involutiveness_k4_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.40/0.60  thf('76', plain,
% 0.40/0.60      (![X45 : $i]:
% 0.40/0.60         (((k4_relat_1 @ (k4_relat_1 @ X45)) = (X45)) | ~ (v1_relat_1 @ X45))),
% 0.40/0.60      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.40/0.60  thf('77', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['75', '76'])).
% 0.40/0.60  thf('78', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '14'])).
% 0.40/0.60  thf('79', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['77', '78'])).
% 0.40/0.60  thf('80', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '79'])).
% 0.40/0.60  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['18', '27'])).
% 0.40/0.60  thf('82', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['80', '81'])).
% 0.40/0.60  thf('83', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['82'])).
% 0.40/0.60  thf('84', plain,
% 0.40/0.60      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.40/0.60        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('85', plain,
% 0.40/0.60      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.40/0.60         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['84'])).
% 0.40/0.60  thf('86', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['71'])).
% 0.40/0.60  thf('87', plain,
% 0.40/0.60      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.60         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['84'])).
% 0.40/0.60  thf('88', plain,
% 0.40/0.60      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.40/0.60         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['86', '87'])).
% 0.40/0.60  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('90', plain,
% 0.40/0.60      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.60         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['88', '89'])).
% 0.40/0.60  thf('91', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['90'])).
% 0.40/0.60  thf('92', plain,
% 0.40/0.60      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.40/0.60       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.40/0.60      inference('split', [status(esa)], ['84'])).
% 0.40/0.60  thf('93', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.40/0.60  thf('94', plain, (((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['85', '93'])).
% 0.40/0.60  thf('95', plain,
% 0.40/0.60      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['83', '94'])).
% 0.40/0.60  thf('96', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('97', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.40/0.60      inference('demod', [status(thm)], ['95', '96'])).
% 0.40/0.60  thf('98', plain, ($false), inference('simplify', [status(thm)], ['97'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
