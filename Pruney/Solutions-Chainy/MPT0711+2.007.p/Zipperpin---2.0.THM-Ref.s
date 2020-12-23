%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bmkRmVjOAB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:12 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 723 expanded)
%              Number of leaves         :   22 ( 229 expanded)
%              Depth                    :   22
%              Number of atoms          : 1193 (10943 expanded)
%              Number of equality atoms :   76 ( 927 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t166_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ! [D: $i] :
                    ( ( r2_hidden @ D @ C )
                   => ( ( k1_funct_1 @ A @ D )
                      = ( k1_funct_1 @ B @ D ) ) ) )
             => ( ( k7_relat_1 @ A @ C )
                = ( k7_relat_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( ( k1_relat_1 @ A )
                    = ( k1_relat_1 @ B ) )
                  & ! [D: $i] :
                      ( ( r2_hidden @ D @ C )
                     => ( ( k1_funct_1 @ A @ D )
                        = ( k1_funct_1 @ B @ D ) ) ) )
               => ( ( k7_relat_1 @ A @ C )
                  = ( k7_relat_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t166_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t165_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                & ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) )
             => ( ( ( k7_relat_1 @ A @ C )
                  = ( k7_relat_1 @ B @ C ) )
              <=> ! [D: $i] :
                    ( ( r2_hidden @ D @ C )
                   => ( ( k1_funct_1 @ A @ D )
                      = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( r2_hidden @ ( sk_D @ X16 @ X15 @ X17 ) @ X16 )
      | ( ( k7_relat_1 @ X17 @ X16 )
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('12',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['10','40','41','42','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('68',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ ( k7_relat_1 @ X6 @ X5 ) ) )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X19: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X19 )
        = ( k1_funct_1 @ sk_B @ X19 ) )
      | ~ ( r2_hidden @ X19 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k1_funct_1 @ X17 @ ( sk_D @ X16 @ X15 @ X17 ) )
       != ( k1_funct_1 @ X15 @ ( sk_D @ X16 @ X15 @ X17 ) ) )
      | ( ( k7_relat_1 @ X17 @ X16 )
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('86',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ sk_A @ sk_B ) ) )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83','84','85','86','87'])).

thf('89',plain,
    ( ( k7_relat_1 @ sk_B @ sk_C )
    = ( k7_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bmkRmVjOAB
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.53/1.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.53/1.76  % Solved by: fo/fo7.sh
% 1.53/1.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.76  % done 1375 iterations in 1.306s
% 1.53/1.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.53/1.76  % SZS output start Refutation
% 1.53/1.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.53/1.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.53/1.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.53/1.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.53/1.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.53/1.76  thf(sk_C_type, type, sk_C: $i).
% 1.53/1.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.53/1.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.53/1.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.53/1.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.53/1.76  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.76  thf(sk_B_type, type, sk_B: $i).
% 1.53/1.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.53/1.76  thf(t166_funct_1, conjecture,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.53/1.76       ( ![B:$i]:
% 1.53/1.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.53/1.76           ( ![C:$i]:
% 1.53/1.76             ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.53/1.76                 ( ![D:$i]:
% 1.53/1.76                   ( ( r2_hidden @ D @ C ) =>
% 1.53/1.76                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 1.53/1.76               ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ))).
% 1.53/1.76  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.76    (~( ![A:$i]:
% 1.53/1.76        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.53/1.76          ( ![B:$i]:
% 1.53/1.76            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.53/1.76              ( ![C:$i]:
% 1.53/1.76                ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.53/1.76                    ( ![D:$i]:
% 1.53/1.76                      ( ( r2_hidden @ D @ C ) =>
% 1.53/1.76                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 1.53/1.76                  ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ) )),
% 1.53/1.76    inference('cnf.neg', [status(esa)], [t166_funct_1])).
% 1.53/1.76  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('1', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(t89_relat_1, axiom,
% 1.53/1.76    (![A:$i,B:$i]:
% 1.53/1.76     ( ( v1_relat_1 @ B ) =>
% 1.53/1.76       ( r1_tarski @
% 1.53/1.76         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 1.53/1.76  thf('2', plain,
% 1.53/1.76      (![X9 : $i, X10 : $i]:
% 1.53/1.76         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X9 @ X10)) @ 
% 1.53/1.76           (k1_relat_1 @ X9))
% 1.53/1.76          | ~ (v1_relat_1 @ X9))),
% 1.53/1.76      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.53/1.76  thf('3', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 1.53/1.76           (k1_relat_1 @ sk_A))
% 1.53/1.76          | ~ (v1_relat_1 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['1', '2'])).
% 1.53/1.76  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('5', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 1.53/1.76          (k1_relat_1 @ sk_A))),
% 1.53/1.76      inference('demod', [status(thm)], ['3', '4'])).
% 1.53/1.76  thf(t165_funct_1, axiom,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.53/1.76       ( ![B:$i]:
% 1.53/1.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.53/1.76           ( ![C:$i]:
% 1.53/1.76             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 1.53/1.76                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 1.53/1.76               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 1.53/1.76                 ( ![D:$i]:
% 1.53/1.76                   ( ( r2_hidden @ D @ C ) =>
% 1.53/1.76                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 1.53/1.76  thf('6', plain,
% 1.53/1.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X15)
% 1.53/1.76          | ~ (v1_funct_1 @ X15)
% 1.53/1.76          | (r2_hidden @ (sk_D @ X16 @ X15 @ X17) @ X16)
% 1.53/1.76          | ((k7_relat_1 @ X17 @ X16) = (k7_relat_1 @ X15 @ X16))
% 1.53/1.76          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X15))
% 1.53/1.76          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 1.53/1.76          | ~ (v1_funct_1 @ X17)
% 1.53/1.76          | ~ (v1_relat_1 @ X17))),
% 1.53/1.76      inference('cnf', [status(esa)], [t165_funct_1])).
% 1.53/1.76  thf('7', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X1)
% 1.53/1.76          | ~ (v1_funct_1 @ X1)
% 1.53/1.76          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 1.53/1.76               (k1_relat_1 @ X1))
% 1.53/1.76          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 1.53/1.76              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 1.53/1.76          | (r2_hidden @ 
% 1.53/1.76             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A @ X1) @ 
% 1.53/1.76             (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 1.53/1.76          | ~ (v1_funct_1 @ sk_A)
% 1.53/1.76          | ~ (v1_relat_1 @ sk_A))),
% 1.53/1.76      inference('sup-', [status(thm)], ['5', '6'])).
% 1.53/1.76  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('10', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X1)
% 1.53/1.76          | ~ (v1_funct_1 @ X1)
% 1.53/1.76          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 1.53/1.76               (k1_relat_1 @ X1))
% 1.53/1.76          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 1.53/1.76              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 1.53/1.76          | (r2_hidden @ 
% 1.53/1.76             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A @ X1) @ 
% 1.53/1.76             (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))),
% 1.53/1.76      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.53/1.76  thf('11', plain,
% 1.53/1.76      (![X9 : $i, X10 : $i]:
% 1.53/1.76         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X9 @ X10)) @ 
% 1.53/1.76           (k1_relat_1 @ X9))
% 1.53/1.76          | ~ (v1_relat_1 @ X9))),
% 1.53/1.76      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.53/1.76  thf('12', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf(t91_relat_1, axiom,
% 1.53/1.76    (![A:$i,B:$i]:
% 1.53/1.76     ( ( v1_relat_1 @ B ) =>
% 1.53/1.76       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.53/1.76         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.53/1.76  thf('13', plain,
% 1.53/1.76      (![X11 : $i, X12 : $i]:
% 1.53/1.76         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 1.53/1.76          | ((k1_relat_1 @ (k7_relat_1 @ X12 @ X11)) = (X11))
% 1.53/1.76          | ~ (v1_relat_1 @ X12))),
% 1.53/1.76      inference('cnf', [status(esa)], [t91_relat_1])).
% 1.53/1.76  thf('14', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 1.53/1.76          | ~ (v1_relat_1 @ sk_B)
% 1.53/1.76          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) = (X0)))),
% 1.53/1.76      inference('sup-', [status(thm)], ['12', '13'])).
% 1.53/1.76  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('16', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 1.53/1.76          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) = (X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['14', '15'])).
% 1.53/1.76  thf('17', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ sk_A)
% 1.53/1.76          | ((k1_relat_1 @ 
% 1.53/1.76              (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 1.53/1.76              = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['11', '16'])).
% 1.53/1.76  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('19', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ 
% 1.53/1.76           (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['17', '18'])).
% 1.53/1.76  thf(t71_relat_1, axiom,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.53/1.76       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.53/1.76  thf('20', plain, (![X2 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 1.53/1.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.53/1.76  thf(t189_relat_1, axiom,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( v1_relat_1 @ A ) =>
% 1.53/1.76       ( ![B:$i]:
% 1.53/1.76         ( ( v1_relat_1 @ B ) =>
% 1.53/1.76           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 1.53/1.76             ( k7_relat_1 @
% 1.53/1.76               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 1.53/1.76  thf('21', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X0)
% 1.53/1.76          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 1.53/1.76              = (k7_relat_1 @ X1 @ 
% 1.53/1.76                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 1.53/1.76          | ~ (v1_relat_1 @ X1))),
% 1.53/1.76      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.53/1.76  thf(t87_relat_1, axiom,
% 1.53/1.76    (![A:$i,B:$i]:
% 1.53/1.76     ( ( v1_relat_1 @ B ) =>
% 1.53/1.76       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.53/1.76  thf('22', plain,
% 1.53/1.76      (![X7 : $i, X8 : $i]:
% 1.53/1.76         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X7 @ X8)) @ X8)
% 1.53/1.76          | ~ (v1_relat_1 @ X7))),
% 1.53/1.76      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.53/1.76  thf('23', plain,
% 1.53/1.76      (![X11 : $i, X12 : $i]:
% 1.53/1.76         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 1.53/1.76          | ((k1_relat_1 @ (k7_relat_1 @ X12 @ X11)) = (X11))
% 1.53/1.76          | ~ (v1_relat_1 @ X12))),
% 1.53/1.76      inference('cnf', [status(esa)], [t91_relat_1])).
% 1.53/1.76  thf('24', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X1)
% 1.53/1.76          | ~ (v1_relat_1 @ X0)
% 1.53/1.76          | ((k1_relat_1 @ 
% 1.53/1.76              (k7_relat_1 @ X0 @ 
% 1.53/1.76               (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))
% 1.53/1.76              = (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['22', '23'])).
% 1.53/1.76  thf('25', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 1.53/1.76            = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 1.53/1.76          | ~ (v1_relat_1 @ X1)
% 1.53/1.76          | ~ (v1_relat_1 @ X0)
% 1.53/1.76          | ~ (v1_relat_1 @ X1)
% 1.53/1.76          | ~ (v1_relat_1 @ X0))),
% 1.53/1.76      inference('sup+', [status(thm)], ['21', '24'])).
% 1.53/1.76  thf('26', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X0)
% 1.53/1.76          | ~ (v1_relat_1 @ X1)
% 1.53/1.76          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 1.53/1.76              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 1.53/1.76      inference('simplify', [status(thm)], ['25'])).
% 1.53/1.76  thf('27', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.53/1.76            = (k1_relat_1 @ 
% 1.53/1.76               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 1.53/1.76          | ~ (v1_relat_1 @ X1)
% 1.53/1.76          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.53/1.76      inference('sup+', [status(thm)], ['20', '26'])).
% 1.53/1.76  thf(fc3_funct_1, axiom,
% 1.53/1.76    (![A:$i]:
% 1.53/1.76     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.53/1.76       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.53/1.76  thf('28', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.53/1.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.53/1.76  thf('29', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.53/1.76            = (k1_relat_1 @ 
% 1.53/1.76               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 1.53/1.76          | ~ (v1_relat_1 @ X1))),
% 1.53/1.76      inference('demod', [status(thm)], ['27', '28'])).
% 1.53/1.76  thf('30', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('31', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X0)
% 1.53/1.76          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 1.53/1.76              = (k7_relat_1 @ X1 @ 
% 1.53/1.76                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 1.53/1.76          | ~ (v1_relat_1 @ X1))),
% 1.53/1.76      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.53/1.76  thf('32', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (((k7_relat_1 @ sk_B @ (k1_relat_1 @ X0))
% 1.53/1.76            = (k7_relat_1 @ sk_B @ 
% 1.53/1.76               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A)))))
% 1.53/1.76          | ~ (v1_relat_1 @ sk_B)
% 1.53/1.76          | ~ (v1_relat_1 @ X0))),
% 1.53/1.76      inference('sup+', [status(thm)], ['30', '31'])).
% 1.53/1.76  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('34', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (((k7_relat_1 @ sk_B @ (k1_relat_1 @ X0))
% 1.53/1.76            = (k7_relat_1 @ sk_B @ 
% 1.53/1.76               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A)))))
% 1.53/1.76          | ~ (v1_relat_1 @ X0))),
% 1.53/1.76      inference('demod', [status(thm)], ['32', '33'])).
% 1.53/1.76  thf('35', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (((k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.53/1.76            = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 1.53/1.76          | ~ (v1_relat_1 @ sk_A)
% 1.53/1.76          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.53/1.76      inference('sup+', [status(thm)], ['29', '34'])).
% 1.53/1.76  thf('36', plain, (![X2 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 1.53/1.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.53/1.76  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('38', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.53/1.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.53/1.76  thf('39', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k7_relat_1 @ sk_B @ X0)
% 1.53/1.76           = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 1.53/1.76      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.53/1.76  thf('40', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['19', '39'])).
% 1.53/1.76  thf('41', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['19', '39'])).
% 1.53/1.76  thf('42', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['19', '39'])).
% 1.53/1.76  thf('43', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('44', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.53/1.76            = (k1_relat_1 @ 
% 1.53/1.76               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 1.53/1.76          | ~ (v1_relat_1 @ X1))),
% 1.53/1.76      inference('demod', [status(thm)], ['27', '28'])).
% 1.53/1.76  thf('45', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76            = (k1_relat_1 @ 
% 1.53/1.76               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ sk_A))))
% 1.53/1.76          | ~ (v1_relat_1 @ sk_B))),
% 1.53/1.76      inference('sup+', [status(thm)], ['43', '44'])).
% 1.53/1.76  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('47', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76           = (k1_relat_1 @ 
% 1.53/1.76              (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ sk_A))))),
% 1.53/1.76      inference('demod', [status(thm)], ['45', '46'])).
% 1.53/1.76  thf('48', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['19', '39'])).
% 1.53/1.76  thf('49', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 1.53/1.76           = (k1_relat_1 @ 
% 1.53/1.76              (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ sk_A))))),
% 1.53/1.76      inference('demod', [status(thm)], ['47', '48'])).
% 1.53/1.76  thf('50', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X0)
% 1.53/1.76          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 1.53/1.76              = (k7_relat_1 @ X1 @ 
% 1.53/1.76                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 1.53/1.76          | ~ (v1_relat_1 @ X1))),
% 1.53/1.76      inference('cnf', [status(esa)], [t189_relat_1])).
% 1.53/1.76  thf('51', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (((k7_relat_1 @ sk_A @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.53/1.76            = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 1.53/1.76          | ~ (v1_relat_1 @ sk_A)
% 1.53/1.76          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.53/1.76      inference('sup+', [status(thm)], ['49', '50'])).
% 1.53/1.76  thf('52', plain, (![X2 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 1.53/1.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.53/1.76  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('54', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.53/1.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.53/1.76  thf('55', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k7_relat_1 @ sk_A @ X0)
% 1.53/1.76           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 1.53/1.76      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 1.53/1.76  thf('56', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['19', '39'])).
% 1.53/1.76  thf('57', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['19', '39'])).
% 1.53/1.76  thf('58', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X1)
% 1.53/1.76          | ~ (v1_funct_1 @ X1)
% 1.53/1.76          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 1.53/1.76               (k1_relat_1 @ X1))
% 1.53/1.76          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 1.53/1.76              = (k7_relat_1 @ sk_A @ X0))
% 1.53/1.76          | (r2_hidden @ 
% 1.53/1.76             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ X1) @ 
% 1.53/1.76             (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 1.53/1.76      inference('demod', [status(thm)],
% 1.53/1.76                ['10', '40', '41', '42', '55', '56', '57'])).
% 1.53/1.76  thf('59', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 1.53/1.76             (k1_relat_1 @ sk_A))
% 1.53/1.76          | (r2_hidden @ 
% 1.53/1.76             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 1.53/1.76             (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 1.53/1.76          | ((k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 1.53/1.76              = (k7_relat_1 @ sk_A @ X0))
% 1.53/1.76          | ~ (v1_funct_1 @ sk_B)
% 1.53/1.76          | ~ (v1_relat_1 @ sk_B))),
% 1.53/1.76      inference('sup-', [status(thm)], ['0', '58'])).
% 1.53/1.76  thf('60', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ 
% 1.53/1.76           (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['17', '18'])).
% 1.53/1.76  thf('61', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 1.53/1.76          (k1_relat_1 @ sk_A))),
% 1.53/1.76      inference('demod', [status(thm)], ['3', '4'])).
% 1.53/1.76  thf('62', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 1.53/1.76          (k1_relat_1 @ sk_A))),
% 1.53/1.76      inference('sup+', [status(thm)], ['60', '61'])).
% 1.53/1.76  thf('63', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k7_relat_1 @ sk_B @ X0)
% 1.53/1.76           = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 1.53/1.76      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.53/1.76  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('66', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((r2_hidden @ 
% 1.53/1.76           (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 1.53/1.76           (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 1.53/1.76          | ((k7_relat_1 @ sk_B @ X0) = (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['59', '62', '63', '64', '65'])).
% 1.53/1.76  thf('67', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.53/1.76           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.53/1.76      inference('demod', [status(thm)], ['19', '39'])).
% 1.53/1.76  thf(t86_relat_1, axiom,
% 1.53/1.76    (![A:$i,B:$i,C:$i]:
% 1.53/1.76     ( ( v1_relat_1 @ C ) =>
% 1.53/1.76       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 1.53/1.76         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 1.53/1.76  thf('68', plain,
% 1.53/1.76      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.53/1.76         (~ (r2_hidden @ X4 @ (k1_relat_1 @ (k7_relat_1 @ X6 @ X5)))
% 1.53/1.76          | (r2_hidden @ X4 @ X5)
% 1.53/1.76          | ~ (v1_relat_1 @ X6))),
% 1.53/1.76      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.53/1.76  thf('69', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 1.53/1.76          | ~ (v1_relat_1 @ sk_B)
% 1.53/1.76          | (r2_hidden @ X1 @ X0))),
% 1.53/1.76      inference('sup-', [status(thm)], ['67', '68'])).
% 1.53/1.76  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('71', plain,
% 1.53/1.76      (![X0 : $i, X1 : $i]:
% 1.53/1.76         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 1.53/1.76          | (r2_hidden @ X1 @ X0))),
% 1.53/1.76      inference('demod', [status(thm)], ['69', '70'])).
% 1.53/1.76  thf('72', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (((k7_relat_1 @ sk_B @ X0) = (k7_relat_1 @ sk_A @ X0))
% 1.53/1.76          | (r2_hidden @ 
% 1.53/1.76             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 1.53/1.76             X0))),
% 1.53/1.76      inference('sup-', [status(thm)], ['66', '71'])).
% 1.53/1.76  thf('73', plain,
% 1.53/1.76      (![X19 : $i]:
% 1.53/1.76         (((k1_funct_1 @ sk_A @ X19) = (k1_funct_1 @ sk_B @ X19))
% 1.53/1.76          | ~ (r2_hidden @ X19 @ sk_C))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('74', plain,
% 1.53/1.76      ((((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 1.53/1.76        | ((k1_funct_1 @ sk_A @ 
% 1.53/1.76            (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ sk_A @ sk_B))
% 1.53/1.76            = (k1_funct_1 @ sk_B @ 
% 1.53/1.76               (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ sk_A @ sk_B))))),
% 1.53/1.76      inference('sup-', [status(thm)], ['72', '73'])).
% 1.53/1.76  thf('75', plain,
% 1.53/1.76      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('76', plain,
% 1.53/1.76      (((k1_funct_1 @ sk_A @ 
% 1.53/1.76         (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ sk_A @ sk_B))
% 1.53/1.76         = (k1_funct_1 @ sk_B @ 
% 1.53/1.76            (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ sk_A @ sk_B)))),
% 1.53/1.76      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 1.53/1.76  thf('77', plain,
% 1.53/1.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.53/1.76         (~ (v1_relat_1 @ X15)
% 1.53/1.76          | ~ (v1_funct_1 @ X15)
% 1.53/1.76          | ((k1_funct_1 @ X17 @ (sk_D @ X16 @ X15 @ X17))
% 1.53/1.76              != (k1_funct_1 @ X15 @ (sk_D @ X16 @ X15 @ X17)))
% 1.53/1.76          | ((k7_relat_1 @ X17 @ X16) = (k7_relat_1 @ X15 @ X16))
% 1.53/1.76          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X15))
% 1.53/1.76          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 1.53/1.76          | ~ (v1_funct_1 @ X17)
% 1.53/1.76          | ~ (v1_relat_1 @ X17))),
% 1.53/1.76      inference('cnf', [status(esa)], [t165_funct_1])).
% 1.53/1.76  thf('78', plain,
% 1.53/1.76      ((((k1_funct_1 @ sk_A @ 
% 1.53/1.76          (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ sk_A @ sk_B))
% 1.53/1.76          != (k1_funct_1 @ sk_A @ 
% 1.53/1.76              (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ sk_A @ sk_B)))
% 1.53/1.76        | ~ (v1_relat_1 @ sk_B)
% 1.53/1.76        | ~ (v1_funct_1 @ sk_B)
% 1.53/1.76        | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.53/1.76             (k1_relat_1 @ sk_B))
% 1.53/1.76        | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.53/1.76             (k1_relat_1 @ sk_A))
% 1.53/1.76        | ((k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 1.53/1.76            = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.53/1.76        | ~ (v1_funct_1 @ sk_A)
% 1.53/1.76        | ~ (v1_relat_1 @ sk_A))),
% 1.53/1.76      inference('sup-', [status(thm)], ['76', '77'])).
% 1.53/1.76  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('81', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('82', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 1.53/1.76          (k1_relat_1 @ sk_A))),
% 1.53/1.76      inference('sup+', [status(thm)], ['60', '61'])).
% 1.53/1.76  thf('83', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 1.53/1.76          (k1_relat_1 @ sk_A))),
% 1.53/1.76      inference('sup+', [status(thm)], ['60', '61'])).
% 1.53/1.76  thf('84', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k7_relat_1 @ sk_B @ X0)
% 1.53/1.76           = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 1.53/1.76      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.53/1.76  thf('85', plain,
% 1.53/1.76      (![X0 : $i]:
% 1.53/1.76         ((k7_relat_1 @ sk_A @ X0)
% 1.53/1.76           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 1.53/1.76      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 1.53/1.76  thf('86', plain, ((v1_funct_1 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('88', plain,
% 1.53/1.76      ((((k1_funct_1 @ sk_A @ 
% 1.53/1.76          (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ sk_A @ sk_B))
% 1.53/1.76          != (k1_funct_1 @ sk_A @ 
% 1.53/1.76              (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ sk_A @ sk_B)))
% 1.53/1.76        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C)))),
% 1.53/1.76      inference('demod', [status(thm)],
% 1.53/1.76                ['78', '79', '80', '81', '82', '83', '84', '85', '86', '87'])).
% 1.53/1.76  thf('89', plain, (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))),
% 1.53/1.76      inference('simplify', [status(thm)], ['88'])).
% 1.53/1.76  thf('90', plain,
% 1.53/1.76      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 1.53/1.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.76  thf('91', plain, ($false),
% 1.53/1.76      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 1.53/1.76  
% 1.53/1.76  % SZS output end Refutation
% 1.53/1.76  
% 1.53/1.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
