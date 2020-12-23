%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OcH1EUZYfD

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 117 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  695 (1316 expanded)
%              Number of equality atoms :   37 (  77 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t53_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ? [B: $i] :
              ( ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
              & ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
         => ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_funct_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('2',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('4',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5','6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v2_funct_1 @ X8 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B_1 ) )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B_1 )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t49_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) )
                    & ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) )
                    & ( ( k1_relat_1 @ B )
                      = ( k1_relat_1 @ C ) )
                    & ( ( k5_relat_1 @ B @ A )
                      = ( k5_relat_1 @ C @ A ) ) )
                 => ( B = C ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( sk_B @ X10 ) )
      | ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X10 ) ) @ ( k1_relat_1 @ X10 ) )
      | ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X3 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k5_relat_1 @ ( sk_B @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( sk_B @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( sk_B @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( sk_B @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( sk_B @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( sk_B @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_B @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( sk_B @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_B @ ( k6_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( sk_B @ X10 ) @ X10 )
        = ( k5_relat_1 @ ( sk_C @ X10 ) @ X10 ) )
      | ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X10 ) )
      | ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ X10 ) ) @ ( k1_relat_1 @ X10 ) )
      | ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ( ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X3 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( sk_C @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( sk_C @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( sk_C @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( sk_C @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( sk_B @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( sk_B @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( sk_B @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( sk_B @ ( k6_relat_1 @ X0 ) )
        = ( sk_C @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( ( sk_B @ X10 )
       != ( sk_C @ X10 ) )
      | ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k6_relat_1 @ X0 ) )
       != ( sk_B @ ( k6_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k6_relat_1 @ X0 ) )
       != ( sk_B @ ( k6_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['19','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OcH1EUZYfD
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.21/0.34  % Python version: Python 3.6.8
% 0.21/0.34  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 48 iterations in 0.038s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.48  thf(t53_funct_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( ?[B:$i]:
% 0.21/0.48           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.48             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.21/0.48         ( v2_funct_1 @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48          ( ( ?[B:$i]:
% 0.21/0.48              ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.48                ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.21/0.48            ( v2_funct_1 @ A ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t53_funct_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (((k5_relat_1 @ sk_A @ sk_B_1) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t27_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.21/0.48             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X6)
% 0.21/0.48          | ~ (v1_funct_1 @ X6)
% 0.21/0.48          | (r1_tarski @ (k2_relat_1 @ X6) @ (k1_relat_1 @ X7))
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X6 @ X7)) != (k1_relat_1 @ X6))
% 0.21/0.48          | ~ (v1_funct_1 @ X7)
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.21/0.48          != (k1_relat_1 @ sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.48        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.48        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t71_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.48  thf('3', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.48  thf('4', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.21/0.48        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3', '4', '5', '6', '7'])).
% 0.21/0.48  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf(t47_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.21/0.48               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.48             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X8)
% 0.21/0.48          | ~ (v1_funct_1 @ X8)
% 0.21/0.48          | (v2_funct_1 @ X8)
% 0.21/0.48          | ~ (r1_tarski @ (k2_relat_1 @ X8) @ (k1_relat_1 @ X9))
% 0.21/0.48          | ~ (v2_funct_1 @ (k5_relat_1 @ X8 @ X9))
% 0.21/0.48          | ~ (v1_funct_1 @ X9)
% 0.21/0.48          | ~ (v1_relat_1 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.48        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B_1))
% 0.21/0.48        | (v2_funct_1 @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((k5_relat_1 @ sk_A @ sk_B_1) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.21/0.48        | (v2_funct_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '16'])).
% 0.21/0.48  thf('18', plain, (~ (v2_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, (~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.48  thf(t49_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.48         ( ![B:$i]:
% 0.21/0.48           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48             ( ![C:$i]:
% 0.21/0.48               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48                 ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.48                     ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.48                     ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.48                     ( ( k5_relat_1 @ B @ A ) = ( k5_relat_1 @ C @ A ) ) ) =>
% 0.21/0.49                   ( ( B ) = ( C ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (sk_B @ X10))
% 0.21/0.49          | (v2_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         ((r1_tarski @ (k2_relat_1 @ (sk_B @ X10)) @ (k1_relat_1 @ X10))
% 0.21/0.49          | (v2_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.21/0.49  thf(t79_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.49         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.21/0.49          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X3)) = (X2))
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.49          | ((k5_relat_1 @ (sk_B @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.49              = (sk_B @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v2_funct_1 @ X0)
% 0.21/0.49          | ((k5_relat_1 @ (sk_B @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.49              = (sk_B @ X0))
% 0.21/0.49          | (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (sk_B @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.49            = (sk_B @ X0))
% 0.21/0.49          | (v2_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (sk_B @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49            = (sk_B @ (k6_relat_1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['20', '26'])).
% 0.21/0.49  thf(fc3_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('28', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('29', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (sk_B @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49            = (sk_B @ (k6_relat_1 @ X0)))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (sk_B @ X10) @ X10)
% 0.21/0.49            = (k5_relat_1 @ (sk_C @ X10) @ X10))
% 0.21/0.49          | (v2_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (sk_C @ X10))
% 0.21/0.49          | (v2_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.21/0.49  thf('33', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         ((r1_tarski @ (k2_relat_1 @ (sk_C @ X10)) @ (k1_relat_1 @ X10))
% 0.21/0.49          | (v2_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (k2_relat_1 @ (sk_C @ (k6_relat_1 @ X0))) @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('37', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (k2_relat_1 @ (sk_C @ (k6_relat_1 @ X0))) @ X0)
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.21/0.49          | ((k5_relat_1 @ X2 @ (k6_relat_1 @ X3)) = (X2))
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_C @ (k6_relat_1 @ X0)))
% 0.21/0.49          | ((k5_relat_1 @ (sk_C @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49              = (sk_C @ (k6_relat_1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ((k5_relat_1 @ (sk_C @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49              = (sk_C @ (k6_relat_1 @ X0)))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '40'])).
% 0.21/0.49  thf('42', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('43', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ((k5_relat_1 @ (sk_C @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49              = (sk_C @ (k6_relat_1 @ X0)))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (sk_C @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49            = (sk_C @ (k6_relat_1 @ X0)))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (sk_B @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49            = (sk_C @ (k6_relat_1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['31', '45'])).
% 0.21/0.49  thf('47', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('48', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k5_relat_1 @ (sk_B @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49            = (sk_C @ (k6_relat_1 @ X0)))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ((k5_relat_1 @ (sk_B @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.21/0.49              = (sk_C @ (k6_relat_1 @ X0))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B @ (k6_relat_1 @ X0)) = (sk_C @ (k6_relat_1 @ X0)))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['30', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ((sk_B @ (k6_relat_1 @ X0)) = (sk_C @ (k6_relat_1 @ X0))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         (((sk_B @ X10) != (sk_C @ X10))
% 0.21/0.49          | (v2_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B @ (k6_relat_1 @ X0)) != (sk_B @ (k6_relat_1 @ X0)))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('56', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B @ (k6_relat_1 @ X0)) != (sk_B @ (k6_relat_1 @ X0)))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.49  thf('58', plain, (![X0 : $i]: (v2_funct_1 @ (k6_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.49  thf('59', plain, ($false), inference('demod', [status(thm)], ['19', '58'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
