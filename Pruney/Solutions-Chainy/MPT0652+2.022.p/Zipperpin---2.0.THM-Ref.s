%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QAQT7FiPsM

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 132 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   27
%              Number of atoms          :  721 (1703 expanded)
%              Number of equality atoms :   63 ( 153 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( ( k10_relat_1 @ X3 @ ( k2_relat_1 @ X3 ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k10_relat_1 @ X5 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t59_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
              = ( k2_relat_1 @ A ) )
            & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_funct_1])).

thf('13',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('18',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('20',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('21',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('41',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','41'])).

thf('43',plain,
    ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ( k1_relat_1 @ ( k4_relat_1 @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QAQT7FiPsM
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 41 iterations in 0.023s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.48  thf(t37_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.21/0.48         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X6 : $i]:
% 0.21/0.48         (((k2_relat_1 @ X6) = (k1_relat_1 @ (k4_relat_1 @ X6)))
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.48  thf(dt_k2_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.48         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.21/0.48          | ~ (v1_funct_1 @ X8)
% 0.21/0.48          | ~ (v1_relat_1 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf(d9_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X7 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X7)
% 0.21/0.48          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 0.21/0.48          | ~ (v1_funct_1 @ X7)
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.21/0.48          | ~ (v1_funct_1 @ X8)
% 0.21/0.48          | ~ (v1_relat_1 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X6 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X6) = (k2_relat_1 @ (k4_relat_1 @ X6)))
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.48  thf(t169_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X3 : $i]:
% 0.21/0.48         (((k10_relat_1 @ X3 @ (k2_relat_1 @ X3)) = (k1_relat_1 @ X3))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.48            = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.48              = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k10_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.48            = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.21/0.48          | ~ (v2_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X7 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X7)
% 0.21/0.48          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 0.21/0.48          | ~ (v1_funct_1 @ X7)
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.48  thf(t182_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.48             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X4)
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.21/0.48              = (k10_relat_1 @ X5 @ (k1_relat_1 @ X4)))
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.48  thf(t59_funct_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( v2_funct_1 @ A ) =>
% 0.21/0.48         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.48             ( k2_relat_1 @ A ) ) & 
% 0.21/0.48           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.48             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48          ( ( v2_funct_1 @ A ) =>
% 0.21/0.48            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.48                ( k2_relat_1 @ A ) ) & 
% 0.21/0.48              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.21/0.48                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48          != (k2_relat_1 @ sk_A))
% 0.21/0.48        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48            != (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48          != (k2_relat_1 @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.21/0.48          | ~ (v1_funct_1 @ X8)
% 0.21/0.48          | ~ (v1_relat_1 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.48  thf(t146_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X6 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X6) = (k2_relat_1 @ (k4_relat_1 @ X6)))
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X7 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X7)
% 0.21/0.48          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 0.21/0.48          | ~ (v1_funct_1 @ X7)
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.48  thf(t160_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.48             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X1)
% 0.21/0.48          | ((k2_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 0.21/0.48              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X2)))
% 0.21/0.48          | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48          != (k2_relat_1 @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['13'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.48           != (k2_relat_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.48           != (k2_relat_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.48           != (k2_relat_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.48         | ~ (v1_funct_1 @ sk_A)
% 0.21/0.48         | ~ (v2_funct_1 @ sk_A)
% 0.21/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '23'])).
% 0.21/0.48  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.21/0.48           != (k2_relat_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '28'])).
% 0.21/0.48  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '31'])).
% 0.21/0.48  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.21/0.48         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48                = (k2_relat_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '35'])).
% 0.21/0.48  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48          = (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48          = (k2_relat_1 @ sk_A))) | 
% 0.21/0.48       ~
% 0.21/0.48       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48          = (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['13'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (~
% 0.21/0.48       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48          = (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.21/0.48         != (k2_relat_1 @ sk_A))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['14', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      ((((k10_relat_1 @ (k2_funct_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.21/0.48          != (k2_relat_1 @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '42'])).
% 0.21/0.48  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((((k10_relat_1 @ (k2_funct_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.21/0.48          != (k2_relat_1 @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      ((((k10_relat_1 @ (k4_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.21/0.48          != (k2_relat_1 @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.48        | ~ (v2_funct_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '45'])).
% 0.21/0.48  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('48', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('49', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((((k10_relat_1 @ (k4_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))
% 0.21/0.48          != (k2_relat_1 @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      ((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.48        | ~ (v2_funct_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '50'])).
% 0.21/0.48  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('53', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('54', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      ((((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.48        | ((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '55'])).
% 0.21/0.48  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('58', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      (((k1_relat_1 @ (k4_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '59'])).
% 0.21/0.48  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('62', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.48  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
