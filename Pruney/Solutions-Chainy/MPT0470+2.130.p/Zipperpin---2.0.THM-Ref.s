%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2DpWYVPAKo

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 220 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  916 (1574 expanded)
%              Number of equality atoms :   98 ( 187 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X53 @ X54 ) )
        = ( k2_relat_1 @ X54 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) )
        = ( k2_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('13',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('17',plain,(
    ! [X45: $i] :
      ( ( v1_relat_1 @ X45 )
      | ( r2_hidden @ ( sk_B @ X45 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('19',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X38 @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('20',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','22'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('24',plain,(
    ! [X50: $i] :
      ( ( ( k3_xboole_0 @ X50 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('30',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ ( k4_xboole_0 @ X34 @ X36 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X34 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','43'])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

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

thf('48',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X52 @ X51 ) )
        = ( k1_relat_1 @ X52 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X52 ) @ ( k1_relat_1 @ X51 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X50: $i] :
      ( ( ( k3_xboole_0 @ X50 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('64',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('67',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','68'])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('74',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('75',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','75'])).

thf('77',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('81',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['48'])).

thf('86',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','86'])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2DpWYVPAKo
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 245 iterations in 0.100s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.58  thf(dt_k5_relat_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.22/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      (![X48 : $i, X49 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X48)
% 0.22/0.58          | ~ (v1_relat_1 @ X49)
% 0.22/0.58          | (v1_relat_1 @ (k5_relat_1 @ X48 @ X49)))),
% 0.22/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.58  thf(t92_xboole_1, axiom,
% 0.22/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.58  thf('1', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf(t2_boole, axiom,
% 0.22/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.58  thf('2', plain,
% 0.22/0.58      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.58  thf(t100_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.58  thf('3', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.58           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.58  thf('4', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.58  thf('5', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.22/0.58           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['1', '4'])).
% 0.22/0.58  thf('6', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf(t60_relat_1, axiom,
% 0.22/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.58  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      (![X0 : $i]: ((k1_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.58  thf(t47_relat_1, axiom,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ A ) =>
% 0.22/0.58       ( ![B:$i]:
% 0.22/0.58         ( ( v1_relat_1 @ B ) =>
% 0.22/0.58           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.58             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      (![X53 : $i, X54 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X53)
% 0.22/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X53 @ X54)) = (k2_relat_1 @ X54))
% 0.22/0.58          | ~ (r1_tarski @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X53))
% 0.22/0.58          | ~ (v1_relat_1 @ X54))),
% 0.22/0.58      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.22/0.58  thf('10', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.22/0.58          | ~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1))
% 0.22/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k5_xboole_0 @ X1 @ X1)))
% 0.22/0.58              = (k2_relat_1 @ (k5_xboole_0 @ X1 @ X1)))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.58  thf('11', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.58  thf('12', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.58  thf('14', plain,
% 0.22/0.58      (![X0 : $i]: ((k2_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.58  thf('15', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1))
% 0.22/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k5_xboole_0 @ X1 @ X1)))
% 0.22/0.58              = (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['10', '11', '14'])).
% 0.22/0.58  thf('16', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf(d1_relat_1, axiom,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ A ) <=>
% 0.22/0.58       ( ![B:$i]:
% 0.22/0.58         ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.58              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (![X45 : $i]: ((v1_relat_1 @ X45) | (r2_hidden @ (sk_B @ X45) @ X45))),
% 0.22/0.58      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.22/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.58  thf('18', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.22/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.58  thf(t55_zfmisc_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.22/0.58  thf('19', plain,
% 0.22/0.58      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.58         (~ (r1_xboole_0 @ (k2_tarski @ X38 @ X39) @ X40)
% 0.22/0.58          | ~ (r2_hidden @ X38 @ X40))),
% 0.22/0.58      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.22/0.58  thf('20', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.58  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.22/0.58  thf('22', plain, (![X0 : $i]: (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['16', '21'])).
% 0.22/0.58  thf('23', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k5_xboole_0 @ X1 @ X1)))
% 0.22/0.58            = (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['15', '22'])).
% 0.22/0.58  thf(t22_relat_1, axiom,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ A ) =>
% 0.22/0.58       ( ( k3_xboole_0 @
% 0.22/0.58           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.22/0.58         ( A ) ) ))).
% 0.22/0.58  thf('24', plain,
% 0.22/0.58      (![X50 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ X50 @ 
% 0.22/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))) = (
% 0.22/0.58            X50))
% 0.22/0.58          | ~ (v1_relat_1 @ X50))),
% 0.22/0.58      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.58  thf('25', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 0.22/0.58            (k2_zfmisc_1 @ 
% 0.22/0.58             (k1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))) @ 
% 0.22/0.58             k1_xboole_0))
% 0.22/0.58            = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.22/0.58          | ~ (v1_relat_1 @ X1)
% 0.22/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.22/0.58      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.58  thf('26', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.58  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.58           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.58  thf('29', plain,
% 0.22/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.58  thf(t125_zfmisc_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.58         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.22/0.58       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.58         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.22/0.58         ((k2_zfmisc_1 @ X37 @ (k4_xboole_0 @ X34 @ X36))
% 0.22/0.58           = (k4_xboole_0 @ (k2_zfmisc_1 @ X37 @ X34) @ 
% 0.22/0.58              (k2_zfmisc_1 @ X37 @ X36)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.22/0.58           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.58  thf('32', plain,
% 0.22/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.58  thf('33', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['26', '34'])).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k1_xboole_0) = (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 0.22/0.58          | ~ (v1_relat_1 @ X1)
% 0.22/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.22/0.58      inference('demod', [status(thm)], ['25', '35', '36'])).
% 0.22/0.58  thf('38', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ 
% 0.22/0.58             (k5_relat_1 @ X1 @ 
% 0.22/0.58              (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))))
% 0.22/0.58          | ~ (v1_relat_1 @ X1)
% 0.22/0.58          | ((k1_xboole_0)
% 0.22/0.58              = (k5_relat_1 @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))))),
% 0.22/0.58      inference('sup-', [status(thm)], ['5', '37'])).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.22/0.58           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['1', '4'])).
% 0.22/0.58  thf('40', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf('41', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['39', '40'])).
% 0.22/0.58  thf('42', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf('43', plain,
% 0.22/0.58      (![X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X1)
% 0.22/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ k1_xboole_0)))),
% 0.22/0.58      inference('demod', [status(thm)], ['38', '41', '42'])).
% 0.22/0.58  thf('44', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.58          | ~ (v1_relat_1 @ X0)
% 0.22/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['0', '43'])).
% 0.22/0.58  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.22/0.58  thf('46', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X0)
% 0.22/0.58          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.58  thf('47', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.58  thf(t62_relat_1, conjecture,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ A ) =>
% 0.22/0.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i]:
% 0.22/0.58        ( ( v1_relat_1 @ A ) =>
% 0.22/0.58          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.58            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.22/0.58  thf('48', plain,
% 0.22/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.22/0.58        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('49', plain,
% 0.22/0.58      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.58      inference('split', [status(esa)], ['48'])).
% 0.22/0.58  thf('50', plain,
% 0.22/0.58      (![X48 : $i, X49 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X48)
% 0.22/0.58          | ~ (v1_relat_1 @ X49)
% 0.22/0.58          | (v1_relat_1 @ (k5_relat_1 @ X48 @ X49)))),
% 0.22/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.58  thf('51', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.22/0.58           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['1', '4'])).
% 0.22/0.58  thf('52', plain,
% 0.22/0.58      (![X0 : $i]: ((k2_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.58  thf(t46_relat_1, axiom,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ A ) =>
% 0.22/0.58       ( ![B:$i]:
% 0.22/0.58         ( ( v1_relat_1 @ B ) =>
% 0.22/0.58           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.58             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.58  thf('53', plain,
% 0.22/0.58      (![X51 : $i, X52 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X51)
% 0.22/0.58          | ((k1_relat_1 @ (k5_relat_1 @ X52 @ X51)) = (k1_relat_1 @ X52))
% 0.22/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X52) @ (k1_relat_1 @ X51))
% 0.22/0.58          | ~ (v1_relat_1 @ X52))),
% 0.22/0.58      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.22/0.58  thf('54', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.22/0.58          | ~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1))
% 0.22/0.58          | ((k1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.22/0.58              = (k1_relat_1 @ (k5_xboole_0 @ X1 @ X1)))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.58  thf('55', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.58  thf('56', plain,
% 0.22/0.58      (![X0 : $i]: ((k1_relat_1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.58  thf('57', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ (k5_xboole_0 @ X1 @ X1))
% 0.22/0.58          | ((k1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.22/0.58              = (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.22/0.58  thf('58', plain, (![X0 : $i]: (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['16', '21'])).
% 0.22/0.58  thf('59', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.22/0.58            = (k1_xboole_0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.58  thf('60', plain,
% 0.22/0.58      (![X50 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ X50 @ 
% 0.22/0.58            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))) = (
% 0.22/0.58            X50))
% 0.22/0.58          | ~ (v1_relat_1 @ X50))),
% 0.22/0.58      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.58  thf('61', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k3_xboole_0 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) @ 
% 0.22/0.58            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.22/0.58             (k2_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))))
% 0.22/0.58            = (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0)
% 0.22/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['59', '60'])).
% 0.22/0.58  thf('62', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf('63', plain,
% 0.22/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.58  thf('64', plain,
% 0.22/0.58      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.58         ((k2_zfmisc_1 @ (k4_xboole_0 @ X34 @ X36) @ X35)
% 0.22/0.58           = (k4_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.22/0.58              (k2_zfmisc_1 @ X36 @ X35)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.22/0.58  thf('65', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.22/0.58           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['63', '64'])).
% 0.22/0.58  thf('66', plain,
% 0.22/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.58  thf('67', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf('68', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.22/0.58  thf('69', plain,
% 0.22/0.58      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['62', '68'])).
% 0.22/0.58  thf('70', plain,
% 0.22/0.58      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.58  thf('71', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k1_xboole_0) = (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0)
% 0.22/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ (k5_xboole_0 @ X1 @ X1) @ X0)))),
% 0.22/0.58      inference('demod', [status(thm)], ['61', '69', '70'])).
% 0.22/0.58  thf('72', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ 
% 0.22/0.58             (k5_relat_1 @ 
% 0.22/0.58              (k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) @ X1))
% 0.22/0.58          | ~ (v1_relat_1 @ X1)
% 0.22/0.58          | ((k1_xboole_0)
% 0.22/0.58              = (k5_relat_1 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['51', '71'])).
% 0.22/0.58  thf('73', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['39', '40'])).
% 0.22/0.58  thf('74', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.58  thf('75', plain,
% 0.22/0.58      (![X1 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.22/0.58          | ~ (v1_relat_1 @ X1)
% 0.22/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1)))),
% 0.22/0.58      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.22/0.58  thf('76', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X0)
% 0.22/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['50', '75'])).
% 0.22/0.58  thf('77', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.22/0.58  thf('78', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X0)
% 0.22/0.58          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.58  thf('79', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.58          | ~ (v1_relat_1 @ X0))),
% 0.22/0.58      inference('simplify', [status(thm)], ['78'])).
% 0.22/0.58  thf('80', plain,
% 0.22/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.22/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('split', [status(esa)], ['48'])).
% 0.22/0.58  thf('81', plain,
% 0.22/0.58      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.22/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.58  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('83', plain,
% 0.22/0.58      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.58      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.58  thf('84', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['83'])).
% 0.22/0.58  thf('85', plain,
% 0.22/0.58      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.58       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.58      inference('split', [status(esa)], ['48'])).
% 0.22/0.58  thf('86', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.58      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.22/0.58  thf('87', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.58      inference('simpl_trail', [status(thm)], ['49', '86'])).
% 0.22/0.58  thf('88', plain,
% 0.22/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['47', '87'])).
% 0.22/0.58  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('90', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['88', '89'])).
% 0.22/0.58  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
