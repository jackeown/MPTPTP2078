%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9ASMwjgfT4

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:28 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 449 expanded)
%              Number of leaves         :   32 ( 151 expanded)
%              Depth                    :   27
%              Number of atoms          :  700 (3097 expanded)
%              Number of equality atoms :   79 ( 374 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X38 @ X37 ) ) @ ( k1_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

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

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X36 @ X35 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X36 ) @ ( k4_relat_1 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X36 @ X35 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X36 ) @ ( k4_relat_1 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','25'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('37',plain,(
    ! [X34: $i] :
      ( ( ( k3_xboole_0 @ X34 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X34 ) @ ( k2_relat_1 @ X34 ) ) )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_zfmisc_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X24: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','42'])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','32'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('48',plain,(
    ! [X33: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X33 ) )
        = X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X40 @ X39 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X39 ) @ ( k4_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','24'])).

thf('55',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','24'])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','32'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('63',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('64',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('69',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['67','68'])).

thf('70',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['61','69'])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(simplify,[status(thm)],['73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9ASMwjgfT4
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:02:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 517 iterations in 0.260s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.52/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.72  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.52/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.72  thf(dt_k5_relat_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.52/0.72       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      (![X31 : $i, X32 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X31)
% 0.52/0.72          | ~ (v1_relat_1 @ X32)
% 0.52/0.72          | (v1_relat_1 @ (k5_relat_1 @ X31 @ X32)))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.52/0.72  thf(t60_relat_1, axiom,
% 0.52/0.72    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.52/0.72     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.72  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.52/0.72  thf(t44_relat_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( v1_relat_1 @ B ) =>
% 0.52/0.72           ( r1_tarski @
% 0.52/0.72             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (![X37 : $i, X38 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X37)
% 0.52/0.72          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X38 @ X37)) @ 
% 0.52/0.72             (k1_relat_1 @ X38))
% 0.52/0.72          | ~ (v1_relat_1 @ X38))),
% 0.52/0.72      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.52/0.72           k1_xboole_0)
% 0.52/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.72          | ~ (v1_relat_1 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.72  thf(cc1_relat_1, axiom,
% 0.52/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.52/0.72  thf('4', plain, (![X29 : $i]: ((v1_relat_1 @ X29) | ~ (v1_xboole_0 @ X29))),
% 0.52/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.52/0.72  thf(t1_boole, axiom,
% 0.52/0.72    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.72  thf('5', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [t1_boole])).
% 0.52/0.72  thf(t46_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      (![X6 : $i, X7 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.52/0.72  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['5', '6'])).
% 0.52/0.72  thf(t62_relat_1, conjecture,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ A ) =>
% 0.52/0.72       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.52/0.72         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i]:
% 0.52/0.72        ( ( v1_relat_1 @ A ) =>
% 0.52/0.72          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.52/0.72            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.52/0.72  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(d10_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.72  thf('9', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.72  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.72      inference('simplify', [status(thm)], ['9'])).
% 0.52/0.72  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['5', '6'])).
% 0.52/0.72  thf(t41_relat_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( v1_relat_1 @ B ) =>
% 0.52/0.72           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.52/0.72             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      (![X35 : $i, X36 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X35)
% 0.52/0.72          | ((k4_relat_1 @ (k6_subset_1 @ X36 @ X35))
% 0.52/0.72              = (k6_subset_1 @ (k4_relat_1 @ X36) @ (k4_relat_1 @ X35)))
% 0.52/0.72          | ~ (v1_relat_1 @ X36))),
% 0.52/0.72      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.52/0.72  thf(redefinition_k6_subset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (![X25 : $i, X26 : $i]:
% 0.52/0.72         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 0.52/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      (![X25 : $i, X26 : $i]:
% 0.52/0.72         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 0.52/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      (![X35 : $i, X36 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X35)
% 0.52/0.72          | ((k4_relat_1 @ (k4_xboole_0 @ X36 @ X35))
% 0.52/0.72              = (k4_xboole_0 @ (k4_relat_1 @ X36) @ (k4_relat_1 @ X35)))
% 0.52/0.72          | ~ (v1_relat_1 @ X36))),
% 0.52/0.72      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.52/0.72  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['5', '6'])).
% 0.52/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.72  thf('17', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.52/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (![X0 : $i, X2 : $i]:
% 0.52/0.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.52/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['16', '19'])).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r1_tarski @ X1 @ (k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)))
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ((X1) = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['15', '20'])).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (((X1) = (k1_xboole_0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (r1_tarski @ X1 @ (k4_relat_1 @ (k4_xboole_0 @ X0 @ X0))))),
% 0.52/0.72      inference('simplify', [status(thm)], ['21'])).
% 0.52/0.72  thf('23', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r1_tarski @ X1 @ (k4_relat_1 @ k1_xboole_0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ((X1) = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['11', '22'])).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['10', '23'])).
% 0.52/0.72  thf('25', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['8', '24'])).
% 0.52/0.72  thf('26', plain,
% 0.52/0.72      (![X0 : $i]: ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['7', '25'])).
% 0.52/0.72  thf(dt_k4_relat_1, axiom,
% 0.52/0.72    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.52/0.72  thf('27', plain,
% 0.52/0.72      (![X30 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X30)) | ~ (v1_relat_1 @ X30))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.52/0.72  thf('28', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))
% 0.52/0.72          | (v1_relat_1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['4', '28'])).
% 0.52/0.72  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['5', '6'])).
% 0.52/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.72  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.72  thf('32', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.72  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['29', '32'])).
% 0.52/0.72  thf('34', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.52/0.72           k1_xboole_0)
% 0.52/0.72          | ~ (v1_relat_1 @ X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['3', '33'])).
% 0.52/0.72  thf('35', plain,
% 0.52/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.72  thf('36', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X0)
% 0.52/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.72  thf(t22_relat_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ A ) =>
% 0.52/0.72       ( ( k3_xboole_0 @
% 0.52/0.72           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.52/0.72         ( A ) ) ))).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      (![X34 : $i]:
% 0.52/0.72         (((k3_xboole_0 @ X34 @ 
% 0.52/0.72            (k2_zfmisc_1 @ (k1_relat_1 @ X34) @ (k2_relat_1 @ X34))) = (
% 0.52/0.72            X34))
% 0.52/0.72          | ~ (v1_relat_1 @ X34))),
% 0.52/0.72      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.52/0.72            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.52/0.72             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.52/0.72            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['36', '37'])).
% 0.52/0.72  thf(t113_zfmisc_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.72  thf('39', plain,
% 0.52/0.72      (![X23 : $i, X24 : $i]:
% 0.52/0.72         (((k2_zfmisc_1 @ X23 @ X24) = (k1_xboole_0))
% 0.52/0.72          | ((X23) != (k1_xboole_0)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.72  thf('40', plain,
% 0.52/0.72      (![X24 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X24) = (k1_xboole_0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['39'])).
% 0.52/0.72  thf(t2_boole, axiom,
% 0.52/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.72  thf('41', plain,
% 0.52/0.72      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.72  thf('42', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.72      inference('demod', [status(thm)], ['38', '40', '41'])).
% 0.52/0.72  thf('43', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '42'])).
% 0.52/0.72  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['29', '32'])).
% 0.52/0.72  thf('45', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.52/0.72      inference('demod', [status(thm)], ['43', '44'])).
% 0.52/0.72  thf('46', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['45'])).
% 0.52/0.72  thf('47', plain,
% 0.52/0.72      (![X30 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X30)) | ~ (v1_relat_1 @ X30))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.52/0.72  thf(involutiveness_k4_relat_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.52/0.72  thf('48', plain,
% 0.52/0.72      (![X33 : $i]:
% 0.52/0.72         (((k4_relat_1 @ (k4_relat_1 @ X33)) = (X33)) | ~ (v1_relat_1 @ X33))),
% 0.52/0.72      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.52/0.72  thf(t54_relat_1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_relat_1 @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( v1_relat_1 @ B ) =>
% 0.52/0.72           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.52/0.72             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.52/0.72  thf('49', plain,
% 0.52/0.72      (![X39 : $i, X40 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X39)
% 0.52/0.72          | ((k4_relat_1 @ (k5_relat_1 @ X40 @ X39))
% 0.52/0.72              = (k5_relat_1 @ (k4_relat_1 @ X39) @ (k4_relat_1 @ X40)))
% 0.52/0.72          | ~ (v1_relat_1 @ X40))),
% 0.52/0.72      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.52/0.72  thf('50', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 0.52/0.72            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ X1)
% 0.52/0.72          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['48', '49'])).
% 0.52/0.72  thf('51', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ X1)
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 0.52/0.72              = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['47', '50'])).
% 0.52/0.72  thf('52', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 0.52/0.72            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 0.52/0.72          | ~ (v1_relat_1 @ X1)
% 0.52/0.72          | ~ (v1_relat_1 @ X0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['51'])).
% 0.52/0.72  thf('53', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k4_relat_1 @ k1_xboole_0)
% 0.52/0.72            = (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0)))
% 0.52/0.72          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0)
% 0.52/0.72          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['46', '52'])).
% 0.52/0.72  thf('54', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['8', '24'])).
% 0.52/0.72  thf('55', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['8', '24'])).
% 0.52/0.72  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.72      inference('demod', [status(thm)], ['29', '32'])).
% 0.52/0.72  thf('57', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.52/0.72          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.52/0.72  thf('58', plain,
% 0.52/0.72      (![X30 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X30)) | ~ (v1_relat_1 @ X30))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.52/0.72  thf('59', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v1_relat_1 @ X0)
% 0.52/0.72          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.52/0.72      inference('clc', [status(thm)], ['57', '58'])).
% 0.52/0.72  thf('60', plain,
% 0.52/0.72      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.52/0.72        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('61', plain,
% 0.52/0.72      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.72         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.52/0.72      inference('split', [status(esa)], ['60'])).
% 0.52/0.72  thf('62', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.52/0.72          | ~ (v1_relat_1 @ X0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['45'])).
% 0.52/0.72  thf('63', plain,
% 0.52/0.72      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.52/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('split', [status(esa)], ['60'])).
% 0.52/0.72  thf('64', plain,
% 0.52/0.72      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.52/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.72  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('66', plain,
% 0.52/0.72      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['64', '65'])).
% 0.52/0.72  thf('67', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['66'])).
% 0.52/0.72  thf('68', plain,
% 0.52/0.72      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.52/0.72       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.72      inference('split', [status(esa)], ['60'])).
% 0.52/0.72  thf('69', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.72      inference('sat_resolution*', [status(thm)], ['67', '68'])).
% 0.52/0.72  thf('70', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.72      inference('simpl_trail', [status(thm)], ['61', '69'])).
% 0.52/0.72  thf('71', plain,
% 0.52/0.72      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['59', '70'])).
% 0.52/0.72  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('73', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['71', '72'])).
% 0.52/0.72  thf('74', plain, ($false), inference('simplify', [status(thm)], ['73'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
