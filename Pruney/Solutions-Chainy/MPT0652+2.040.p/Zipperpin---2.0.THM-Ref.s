%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NfbhPYWgOM

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 103 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   19
%              Number of atoms          :  695 (1390 expanded)
%              Number of equality atoms :   44 (  99 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('3',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

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

thf('19',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('29',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('36',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','36'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NfbhPYWgOM
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 57 iterations in 0.061s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(t55_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) =>
% 0.22/0.52         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.22/0.52           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X7 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X7)
% 0.22/0.52          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 0.22/0.52          | ~ (v1_funct_1 @ X7)
% 0.22/0.52          | ~ (v1_relat_1 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.52  thf(dt_k2_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X6 : $i]:
% 0.22/0.52         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.22/0.52          | ~ (v1_funct_1 @ X6)
% 0.22/0.52          | ~ (v1_relat_1 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X7 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X7)
% 0.22/0.52          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 0.22/0.52          | ~ (v1_funct_1 @ X7)
% 0.22/0.52          | ~ (v1_relat_1 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X6 : $i]:
% 0.22/0.52         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.22/0.52          | ~ (v1_funct_1 @ X6)
% 0.22/0.52          | ~ (v1_relat_1 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf(t58_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) =>
% 0.22/0.52         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.22/0.52             ( k1_relat_1 @ A ) ) & 
% 0.22/0.52           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.22/0.52             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X8 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X8)
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ (k2_funct_1 @ X8)))
% 0.22/0.52              = (k1_relat_1 @ X8))
% 0.22/0.52          | ~ (v1_funct_1 @ X8)
% 0.22/0.52          | ~ (v1_relat_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.22/0.52  thf(t45_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( v1_relat_1 @ B ) =>
% 0.22/0.52           ( r1_tarski @
% 0.22/0.52             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.22/0.52             (k2_relat_1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X0)
% 0.22/0.52          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X7 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X7)
% 0.22/0.52          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 0.22/0.52          | ~ (v1_funct_1 @ X7)
% 0.22/0.52          | ~ (v1_relat_1 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.22/0.52  thf(t46_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( v1_relat_1 @ B ) =>
% 0.22/0.52           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.52             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X2)
% 0.22/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2)) = (k1_relat_1 @ X3))
% 0.22/0.52          | ~ (r1_tarski @ (k2_relat_1 @ X3) @ (k1_relat_1 @ X2))
% 0.22/0.52          | ~ (v1_relat_1 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.22/0.52              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.22/0.52              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.22/0.52              = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.22/0.52              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.22/0.52            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.52  thf(t59_funct_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) =>
% 0.22/0.52         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.22/0.52             ( k2_relat_1 @ A ) ) & 
% 0.22/0.52           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.22/0.52             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52          ( ( v2_funct_1 @ A ) =>
% 0.22/0.52            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.22/0.52                ( k2_relat_1 @ A ) ) & 
% 0.22/0.52              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.22/0.52                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52          != (k2_relat_1 @ sk_A))
% 0.22/0.52        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52            != (k2_relat_1 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52          != (k2_relat_1 @ sk_A)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52                = (k2_relat_1 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X6 : $i]:
% 0.22/0.52         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.22/0.52          | ~ (v1_funct_1 @ X6)
% 0.22/0.52          | ~ (v1_relat_1 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X0)
% 0.22/0.52          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.52  thf(t47_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( v1_relat_1 @ B ) =>
% 0.22/0.52           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.52             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X4)
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X5)) = (k2_relat_1 @ X5))
% 0.22/0.52          | ~ (r1_tarski @ (k1_relat_1 @ X5) @ (k2_relat_1 @ X4))
% 0.22/0.52          | ~ (v1_relat_1 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.22/0.52              = (k2_relat_1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.22/0.52              = (k2_relat_1 @ X0))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.22/0.52              = (k2_relat_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 0.22/0.52            = (k2_relat_1 @ X0))
% 0.22/0.52          | ~ (v2_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52          != (k2_relat_1 @ sk_A)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52                = (k2_relat_1 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.22/0.52         | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52         | ~ (v1_funct_1 @ sk_A)
% 0.22/0.52         | ~ (v2_funct_1 @ sk_A)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52                = (k2_relat_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52                = (k2_relat_1 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52          = (k2_relat_1 @ sk_A)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (~
% 0.22/0.52       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52          = (k2_relat_1 @ sk_A))) | 
% 0.22/0.52       ~
% 0.22/0.52       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52          = (k2_relat_1 @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (~
% 0.22/0.52       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52          = (k2_relat_1 @ sk_A)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.22/0.52         != (k2_relat_1 @ sk_A))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['20', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      ((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '37'])).
% 0.22/0.52  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.22/0.52        | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '42'])).
% 0.22/0.52  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain, ((v2_funct_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('47', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.22/0.52  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
