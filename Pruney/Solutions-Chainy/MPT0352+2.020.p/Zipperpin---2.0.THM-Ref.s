%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xEgR9p0fD0

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:10 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 144 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  690 (1242 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k4_xboole_0 @ X14 @ X13 ) @ ( k4_xboole_0 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ ( k3_tarski @ X27 ) )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('33',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('34',plain,(
    ! [X30: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('35',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X20 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','51','52'])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['26','53'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( r1_tarski @ sk_B @ sk_C )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('62',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ ( k3_tarski @ X27 ) )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('64',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X30: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('66',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xEgR9p0fD0
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 787 iterations in 0.242s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.48/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.69  thf(t31_subset_1, conjecture,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.69       ( ![C:$i]:
% 0.48/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.69           ( ( r1_tarski @ B @ C ) <=>
% 0.48/0.69             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.69    (~( ![A:$i,B:$i]:
% 0.48/0.69        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.69          ( ![C:$i]:
% 0.48/0.69            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.69              ( ( r1_tarski @ B @ C ) <=>
% 0.48/0.69                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.48/0.69  thf('0', plain,
% 0.48/0.69      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.48/0.69           (k3_subset_1 @ sk_A @ sk_B))
% 0.48/0.69        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('1', plain,
% 0.48/0.69      (~
% 0.48/0.69       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.48/0.69       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(d5_subset_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      (![X34 : $i, X35 : $i]:
% 0.48/0.69         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.48/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.48/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.48/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))
% 0.48/0.69        | (r1_tarski @ sk_B @ sk_C))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.48/0.69      inference('split', [status(esa)], ['5'])).
% 0.48/0.69  thf(t34_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ B ) =>
% 0.48/0.69       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X12 @ X13)
% 0.48/0.69          | (r1_tarski @ (k4_xboole_0 @ X14 @ X13) @ (k4_xboole_0 @ X14 @ X12)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      ((![X0 : $i]:
% 0.48/0.69          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.48/0.69         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.48/0.69         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['4', '8'])).
% 0.48/0.69  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (![X34 : $i, X35 : $i]:
% 0.48/0.69         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.48/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.48/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.69  thf('13', plain,
% 0.48/0.69      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.48/0.69         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.48/0.69      inference('demod', [status(thm)], ['9', '12'])).
% 0.48/0.69  thf('14', plain,
% 0.48/0.69      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.48/0.69           (k3_subset_1 @ sk_A @ sk_B)))
% 0.48/0.69         <= (~
% 0.48/0.69             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.48/0.69               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.48/0.69       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.48/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.69  thf('16', plain,
% 0.48/0.69      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.48/0.69       ((r1_tarski @ sk_B @ sk_C))),
% 0.48/0.69      inference('split', [status(esa)], ['5'])).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.48/0.69         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.48/0.69               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.48/0.69      inference('split', [status(esa)], ['5'])).
% 0.48/0.69  thf('18', plain,
% 0.48/0.69      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.48/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.69  thf(t106_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.48/0.69       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.48/0.69  thf('19', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.48/0.69         ((r1_xboole_0 @ X5 @ X7)
% 0.48/0.69          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.48/0.69  thf('20', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.48/0.69          | (r1_xboole_0 @ X0 @ sk_B))),
% 0.48/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.69  thf('21', plain,
% 0.48/0.69      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B))
% 0.48/0.69         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.48/0.69               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['17', '20'])).
% 0.48/0.69  thf(symmetry_r1_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.48/0.69  thf('22', plain,
% 0.48/0.69      (![X3 : $i, X4 : $i]:
% 0.48/0.69         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.48/0.69  thf('23', plain,
% 0.48/0.69      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.48/0.69         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.48/0.69               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.69  thf('24', plain,
% 0.48/0.69      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.48/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf(t39_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.69  thf('25', plain,
% 0.48/0.69      (![X17 : $i, X18 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.48/0.69           = (k2_xboole_0 @ X17 @ X18))),
% 0.48/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.69  thf('26', plain,
% 0.48/0.69      (((k2_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_C))
% 0.48/0.69         = (k2_xboole_0 @ sk_C @ sk_A))),
% 0.48/0.69      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.69  thf('27', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(d2_subset_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( v1_xboole_0 @ A ) =>
% 0.48/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.48/0.69       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      (![X31 : $i, X32 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X31 @ X32)
% 0.48/0.69          | (r2_hidden @ X31 @ X32)
% 0.48/0.69          | (v1_xboole_0 @ X32))),
% 0.48/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.48/0.69  thf('29', plain,
% 0.48/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.69  thf(fc1_subset_1, axiom,
% 0.48/0.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.69  thf('30', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.48/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.48/0.69  thf('31', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('clc', [status(thm)], ['29', '30'])).
% 0.48/0.69  thf(l49_zfmisc_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.48/0.69  thf('32', plain,
% 0.48/0.69      (![X26 : $i, X27 : $i]:
% 0.48/0.69         ((r1_tarski @ X26 @ (k3_tarski @ X27)) | ~ (r2_hidden @ X26 @ X27))),
% 0.48/0.69      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.48/0.69  thf('33', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.69  thf(t99_zfmisc_1, axiom,
% 0.48/0.69    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.48/0.69  thf('34', plain, (![X30 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X30)) = (X30))),
% 0.48/0.69      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.48/0.69  thf('35', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.48/0.69      inference('demod', [status(thm)], ['33', '34'])).
% 0.48/0.69  thf(t36_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.69  thf('36', plain,
% 0.48/0.69      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.48/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.48/0.69  thf(t1_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.48/0.69       ( r1_tarski @ A @ C ) ))).
% 0.48/0.69  thf('37', plain,
% 0.48/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X9 @ X10)
% 0.48/0.69          | ~ (r1_tarski @ X10 @ X11)
% 0.48/0.69          | (r1_tarski @ X9 @ X11))),
% 0.48/0.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.48/0.69  thf('38', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.69  thf('39', plain,
% 0.48/0.69      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_A)),
% 0.48/0.69      inference('sup-', [status(thm)], ['35', '38'])).
% 0.48/0.69  thf(t79_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.48/0.69  thf('40', plain,
% 0.48/0.69      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 0.48/0.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.48/0.69  thf(t69_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.69       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.48/0.69  thf('41', plain,
% 0.48/0.69      (![X19 : $i, X20 : $i]:
% 0.48/0.69         (~ (r1_xboole_0 @ X19 @ X20)
% 0.48/0.69          | ~ (r1_tarski @ X19 @ X20)
% 0.48/0.69          | (v1_xboole_0 @ X19))),
% 0.48/0.69      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.48/0.69  thf('42', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.48/0.69          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.69  thf('43', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['39', '42'])).
% 0.48/0.69  thf(l13_xboole_0, axiom,
% 0.48/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.69  thf('44', plain,
% 0.48/0.69      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.48/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.69  thf('45', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.48/0.69  thf('46', plain,
% 0.48/0.69      (![X17 : $i, X18 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.48/0.69           = (k2_xboole_0 @ X17 @ X18))),
% 0.48/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.69  thf('47', plain,
% 0.48/0.69      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.48/0.69      inference('sup+', [status(thm)], ['45', '46'])).
% 0.48/0.69  thf(commutativity_k2_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.48/0.69  thf('48', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.69  thf('49', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.69  thf(t1_boole, axiom,
% 0.48/0.69    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.69  thf('50', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.48/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.48/0.69  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['49', '50'])).
% 0.48/0.69  thf('52', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.69  thf('53', plain, (((sk_A) = (k2_xboole_0 @ sk_C @ sk_A))),
% 0.48/0.69      inference('demod', [status(thm)], ['47', '48', '51', '52'])).
% 0.48/0.69  thf('54', plain,
% 0.48/0.69      (((k2_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_A))),
% 0.48/0.69      inference('demod', [status(thm)], ['26', '53'])).
% 0.48/0.69  thf(t73_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.48/0.69       ( r1_tarski @ A @ B ) ))).
% 0.48/0.69  thf('55', plain,
% 0.48/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.48/0.69         ((r1_tarski @ X21 @ X22)
% 0.48/0.69          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.48/0.69          | ~ (r1_xboole_0 @ X21 @ X23))),
% 0.48/0.69      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.48/0.69  thf('56', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X0 @ sk_A)
% 0.48/0.69          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.48/0.69          | (r1_tarski @ X0 @ sk_C))),
% 0.48/0.69      inference('sup-', [status(thm)], ['54', '55'])).
% 0.48/0.69  thf('57', plain,
% 0.48/0.69      ((((r1_tarski @ sk_B @ sk_C) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.48/0.69         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.48/0.69               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['23', '56'])).
% 0.48/0.69  thf('58', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('59', plain,
% 0.48/0.69      (![X31 : $i, X32 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X31 @ X32)
% 0.48/0.69          | (r2_hidden @ X31 @ X32)
% 0.48/0.69          | (v1_xboole_0 @ X32))),
% 0.48/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.48/0.69  thf('60', plain,
% 0.48/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.48/0.69  thf('61', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.48/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.48/0.69  thf('62', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('clc', [status(thm)], ['60', '61'])).
% 0.48/0.69  thf('63', plain,
% 0.48/0.69      (![X26 : $i, X27 : $i]:
% 0.48/0.69         ((r1_tarski @ X26 @ (k3_tarski @ X27)) | ~ (r2_hidden @ X26 @ X27))),
% 0.48/0.69      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.48/0.69  thf('64', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.69  thf('65', plain, (![X30 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X30)) = (X30))),
% 0.48/0.69      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.48/0.69  thf('66', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.48/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.48/0.69  thf('67', plain,
% 0.48/0.69      (((r1_tarski @ sk_B @ sk_C))
% 0.48/0.69         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.48/0.69               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.48/0.69      inference('demod', [status(thm)], ['57', '66'])).
% 0.48/0.69  thf('68', plain,
% 0.48/0.69      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('69', plain,
% 0.48/0.69      (~
% 0.48/0.69       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.48/0.69       ((r1_tarski @ sk_B @ sk_C))),
% 0.48/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.48/0.69  thf('70', plain, ($false),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '69'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
