%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n4HqyWNRuN

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 183 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  708 (2900 expanded)
%              Number of equality atoms :   71 ( 315 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('1',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf(t63_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ( ( k5_relat_1 @ A @ B )
                  = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_funct_1])).

thf('2',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(l72_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( ( k2_relat_1 @ B )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X4 )
       != X3 )
      | ( ( k5_relat_1 @ X4 @ X2 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k5_relat_1 @ X2 @ X5 )
       != ( k6_relat_1 @ X3 ) )
      | ( X5 = X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('6',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5 = X4 )
      | ( ( k5_relat_1 @ X2 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ( ( k5_relat_1 @ X4 @ X2 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('21',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('22',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('23',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

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
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('31',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k4_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','19','20','21','28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( X0
        = ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( X0
        = ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k4_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','37'])).

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
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k4_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ( ( k5_relat_1 @ sk_A @ sk_B )
     != ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k4_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('50',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n4HqyWNRuN
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:12 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 83 iterations in 0.081s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.53  thf(fc5_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.20/0.53       ( ( v1_relat_1 @ ( k4_relat_1 @ A ) ) & 
% 0.20/0.53         ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X1 : $i]:
% 0.20/0.53         ((v1_funct_1 @ (k4_relat_1 @ X1))
% 0.20/0.53          | ~ (v2_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X1 : $i]:
% 0.20/0.53         ((v1_relat_1 @ (k4_relat_1 @ X1))
% 0.20/0.53          | ~ (v2_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.20/0.53  thf(t63_funct_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53           ( ( ( v2_funct_1 @ A ) & 
% 0.20/0.53               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.53               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.20/0.53             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53              ( ( ( v2_funct_1 @ A ) & 
% 0.20/0.53                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.53                  ( ( k5_relat_1 @ A @ B ) =
% 0.20/0.53                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.20/0.53                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.20/0.53  thf('2', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t61_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ( v2_funct_1 @ A ) =>
% 0.20/0.53         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.20/0.53             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.20/0.53           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.20/0.53             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X7 : $i]:
% 0.20/0.53         (~ (v2_funct_1 @ X7)
% 0.20/0.53          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 0.20/0.53              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.20/0.53  thf(t55_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ( v2_funct_1 @ A ) =>
% 0.20/0.53         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.20/0.53           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X6 : $i]:
% 0.20/0.53         (~ (v2_funct_1 @ X6)
% 0.20/0.53          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 0.20/0.53          | ~ (v1_funct_1 @ X6)
% 0.20/0.53          | ~ (v1_relat_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.53  thf(l72_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.53           ( ![D:$i]:
% 0.20/0.53             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.20/0.53               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.53                   ( ( k5_relat_1 @ B @ C ) =
% 0.20/0.53                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.20/0.53                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.20/0.53                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X2)
% 0.20/0.53          | ~ (v1_funct_1 @ X2)
% 0.20/0.53          | ((k2_relat_1 @ X4) != (X3))
% 0.20/0.53          | ((k5_relat_1 @ X4 @ X2) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.20/0.53          | ((k5_relat_1 @ X2 @ X5) != (k6_relat_1 @ X3))
% 0.20/0.53          | ((X5) = (X4))
% 0.20/0.53          | ~ (v1_funct_1 @ X5)
% 0.20/0.53          | ~ (v1_relat_1 @ X5)
% 0.20/0.53          | ~ (v1_funct_1 @ X4)
% 0.20/0.53          | ~ (v1_relat_1 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [l72_funct_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X4)
% 0.20/0.53          | ~ (v1_funct_1 @ X4)
% 0.20/0.53          | ~ (v1_relat_1 @ X5)
% 0.20/0.53          | ~ (v1_funct_1 @ X5)
% 0.20/0.53          | ((X5) = (X4))
% 0.20/0.53          | ((k5_relat_1 @ X2 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.20/0.53          | ((k5_relat_1 @ X4 @ X2) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.20/0.53          | ~ (v1_funct_1 @ X2)
% 0.20/0.53          | ~ (v1_relat_1 @ X2))),
% 0.20/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (((k5_relat_1 @ X2 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X2)
% 0.20/0.53          | ~ (v1_funct_1 @ X2)
% 0.20/0.53          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X2)
% 0.20/0.53              != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.20/0.53          | ((X1) = (k2_funct_1 @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ((X1) = (k2_funct_1 @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k5_relat_1 @ X0 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k5_relat_1 @ X0 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.20/0.53          | ((X1) = (k2_funct_1 @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.53          | ~ (v2_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.20/0.53              != (k6_relat_1 @ (k1_relat_1 @ X1))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.20/0.53            != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53          | ~ (v2_funct_1 @ sk_A)
% 0.20/0.53          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((X0) = (k2_funct_1 @ sk_A))
% 0.20/0.53          | ((k5_relat_1 @ sk_A @ X0) != (k6_relat_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.53  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d9_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v2_funct_1 @ X0)
% 0.20/0.53          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.53        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.20/0.53        | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('18', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.53  thf('20', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.53  thf('21', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.53  thf('22', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X6 : $i]:
% 0.20/0.53         (~ (v2_funct_1 @ X6)
% 0.20/0.53          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 0.20/0.53          | ~ (v1_funct_1 @ X6)
% 0.20/0.53          | ~ (v1_relat_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53        | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((k1_relat_1 @ sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((k5_relat_1 @ sk_A @ sk_B)
% 0.20/0.53         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.20/0.53            != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((X0) = (k4_relat_1 @ sk_A))
% 0.20/0.53          | ((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['10', '11', '12', '13', '19', '20', '21', '28', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ sk_A)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53          | ~ (v2_funct_1 @ sk_A)
% 0.20/0.53          | ((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B))
% 0.20/0.53          | ((X0) = (k4_relat_1 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.53          | ((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.20/0.53              != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '32'])).
% 0.20/0.53  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B))
% 0.20/0.53          | ((X0) = (k4_relat_1 @ sk_A))
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.53          | ((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.20/0.53              != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ sk_A)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53          | ~ (v2_funct_1 @ sk_A)
% 0.20/0.53          | ((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.20/0.53              != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((X0) = (k4_relat_1 @ sk_A))
% 0.20/0.53          | ((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '37'])).
% 0.20/0.53  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.20/0.53            != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((X0) = (k4_relat_1 @ sk_A))
% 0.20/0.53          | ((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((((k5_relat_1 @ sk_A @ sk_B) != (k5_relat_1 @ sk_A @ sk_B))
% 0.20/0.53        | ((sk_B) = (k4_relat_1 @ sk_A))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.53      inference('eq_res', [status(thm)], ['42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.53        | ((sk_B) = (k4_relat_1 @ sk_A)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.53  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.53  thf('48', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.53  thf('50', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['47', '50'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
