%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZsiqooL1Xg

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:12 EST 2020

% Result     : Theorem 3.70s
% Output     : Refutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 911 expanded)
%              Number of leaves         :   21 ( 294 expanded)
%              Depth                    :   21
%              Number of atoms          : 1303 (12034 expanded)
%              Number of equality atoms :   85 ( 969 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('11',plain,(
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

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
       != ( k6_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('19',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['10','34','35','36','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('66',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','60','71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('76',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X4 @ X3 ) ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    ! [X22: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X22 )
        = ( k1_funct_1 @ sk_B @ X22 ) )
      | ~ ( r2_hidden @ X22 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_C_1 )
      = ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
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

thf('89',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('97',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_A @ sk_B ) ) )
    | ( ( k7_relat_1 @ sk_B @ sk_C_1 )
      = ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93','94','95','96','97','98'])).

thf('100',plain,
    ( ( k7_relat_1 @ sk_B @ sk_C_1 )
    = ( k7_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZsiqooL1Xg
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 3.70/3.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.70/3.88  % Solved by: fo/fo7.sh
% 3.70/3.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.70/3.88  % done 2839 iterations in 3.423s
% 3.70/3.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.70/3.88  % SZS output start Refutation
% 3.70/3.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.70/3.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.70/3.88  thf(sk_A_type, type, sk_A: $i).
% 3.70/3.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.70/3.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.70/3.88  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.70/3.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.70/3.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.70/3.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.70/3.88  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.70/3.88  thf(sk_B_type, type, sk_B: $i).
% 3.70/3.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.70/3.88  thf(t166_funct_1, conjecture,
% 3.70/3.88    (![A:$i]:
% 3.70/3.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.70/3.88       ( ![B:$i]:
% 3.70/3.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.70/3.88           ( ![C:$i]:
% 3.70/3.88             ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.70/3.88                 ( ![D:$i]:
% 3.70/3.88                   ( ( r2_hidden @ D @ C ) =>
% 3.70/3.88                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 3.70/3.88               ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ))).
% 3.70/3.88  thf(zf_stmt_0, negated_conjecture,
% 3.70/3.88    (~( ![A:$i]:
% 3.70/3.88        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.70/3.88          ( ![B:$i]:
% 3.70/3.88            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.70/3.88              ( ![C:$i]:
% 3.70/3.88                ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.70/3.88                    ( ![D:$i]:
% 3.70/3.88                      ( ( r2_hidden @ D @ C ) =>
% 3.70/3.88                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 3.70/3.88                  ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ) )),
% 3.70/3.88    inference('cnf.neg', [status(esa)], [t166_funct_1])).
% 3.70/3.88  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('1', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf(t89_relat_1, axiom,
% 3.70/3.88    (![A:$i,B:$i]:
% 3.70/3.88     ( ( v1_relat_1 @ B ) =>
% 3.70/3.88       ( r1_tarski @
% 3.70/3.88         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 3.70/3.88  thf('2', plain,
% 3.70/3.88      (![X7 : $i, X8 : $i]:
% 3.70/3.88         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X7 @ X8)) @ 
% 3.70/3.88           (k1_relat_1 @ X7))
% 3.70/3.88          | ~ (v1_relat_1 @ X7))),
% 3.70/3.88      inference('cnf', [status(esa)], [t89_relat_1])).
% 3.70/3.88  thf('3', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 3.70/3.88           (k1_relat_1 @ sk_A))
% 3.70/3.88          | ~ (v1_relat_1 @ sk_B))),
% 3.70/3.88      inference('sup+', [status(thm)], ['1', '2'])).
% 3.70/3.88  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('5', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 3.70/3.88          (k1_relat_1 @ sk_A))),
% 3.70/3.88      inference('demod', [status(thm)], ['3', '4'])).
% 3.70/3.88  thf(t165_funct_1, axiom,
% 3.70/3.88    (![A:$i]:
% 3.70/3.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.70/3.88       ( ![B:$i]:
% 3.70/3.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.70/3.88           ( ![C:$i]:
% 3.70/3.88             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 3.70/3.88                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 3.70/3.88               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 3.70/3.88                 ( ![D:$i]:
% 3.70/3.88                   ( ( r2_hidden @ D @ C ) =>
% 3.70/3.88                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 3.70/3.88  thf('6', plain,
% 3.70/3.88      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X15)
% 3.70/3.88          | ~ (v1_funct_1 @ X15)
% 3.70/3.88          | (r2_hidden @ (sk_D @ X16 @ X15 @ X17) @ X16)
% 3.70/3.88          | ((k7_relat_1 @ X17 @ X16) = (k7_relat_1 @ X15 @ X16))
% 3.70/3.88          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X15))
% 3.70/3.88          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 3.70/3.88          | ~ (v1_funct_1 @ X17)
% 3.70/3.88          | ~ (v1_relat_1 @ X17))),
% 3.70/3.88      inference('cnf', [status(esa)], [t165_funct_1])).
% 3.70/3.88  thf('7', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_funct_1 @ X1)
% 3.70/3.88          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 3.70/3.88               (k1_relat_1 @ X1))
% 3.70/3.88          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 3.70/3.88              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 3.70/3.88          | (r2_hidden @ 
% 3.70/3.88             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A @ X1) @ 
% 3.70/3.88             (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 3.70/3.88          | ~ (v1_funct_1 @ sk_A)
% 3.70/3.88          | ~ (v1_relat_1 @ sk_A))),
% 3.70/3.88      inference('sup-', [status(thm)], ['5', '6'])).
% 3.70/3.88  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('10', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_funct_1 @ X1)
% 3.70/3.88          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 3.70/3.88               (k1_relat_1 @ X1))
% 3.70/3.88          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 3.70/3.88              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 3.70/3.88          | (r2_hidden @ 
% 3.70/3.88             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A @ X1) @ 
% 3.70/3.88             (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))),
% 3.70/3.88      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.70/3.88  thf(t189_relat_1, axiom,
% 3.70/3.88    (![A:$i]:
% 3.70/3.88     ( ( v1_relat_1 @ A ) =>
% 3.70/3.88       ( ![B:$i]:
% 3.70/3.88         ( ( v1_relat_1 @ B ) =>
% 3.70/3.88           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 3.70/3.88             ( k7_relat_1 @
% 3.70/3.88               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 3.70/3.88  thf('11', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X0)
% 3.70/3.88          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 3.70/3.88              = (k7_relat_1 @ X1 @ 
% 3.70/3.88                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1))),
% 3.70/3.88      inference('cnf', [status(esa)], [t189_relat_1])).
% 3.70/3.88  thf(t87_relat_1, axiom,
% 3.70/3.88    (![A:$i,B:$i]:
% 3.70/3.88     ( ( v1_relat_1 @ B ) =>
% 3.70/3.88       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 3.70/3.88  thf('12', plain,
% 3.70/3.88      (![X5 : $i, X6 : $i]:
% 3.70/3.88         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X5 @ X6)) @ X6)
% 3.70/3.88          | ~ (v1_relat_1 @ X5))),
% 3.70/3.88      inference('cnf', [status(esa)], [t87_relat_1])).
% 3.70/3.88  thf(t91_relat_1, axiom,
% 3.70/3.88    (![A:$i,B:$i]:
% 3.70/3.88     ( ( v1_relat_1 @ B ) =>
% 3.70/3.88       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.70/3.88         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.70/3.88  thf('13', plain,
% 3.70/3.88      (![X9 : $i, X10 : $i]:
% 3.70/3.88         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 3.70/3.88          | ((k1_relat_1 @ (k7_relat_1 @ X10 @ X9)) = (X9))
% 3.70/3.88          | ~ (v1_relat_1 @ X10))),
% 3.70/3.88      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.70/3.88  thf('14', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_relat_1 @ X0)
% 3.70/3.88          | ((k1_relat_1 @ 
% 3.70/3.88              (k7_relat_1 @ X0 @ 
% 3.70/3.88               (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))
% 3.70/3.88              = (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))),
% 3.70/3.88      inference('sup-', [status(thm)], ['12', '13'])).
% 3.70/3.88  thf('15', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 3.70/3.88            = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_relat_1 @ X0)
% 3.70/3.88          | ~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_relat_1 @ X0))),
% 3.70/3.88      inference('sup+', [status(thm)], ['11', '14'])).
% 3.70/3.88  thf('16', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X0)
% 3.70/3.88          | ~ (v1_relat_1 @ X1)
% 3.70/3.88          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 3.70/3.88              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 3.70/3.88      inference('simplify', [status(thm)], ['15'])).
% 3.70/3.88  thf('17', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf(t34_funct_1, axiom,
% 3.70/3.88    (![A:$i,B:$i]:
% 3.70/3.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.70/3.88       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 3.70/3.88         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 3.70/3.88           ( ![C:$i]:
% 3.70/3.88             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 3.70/3.88  thf('18', plain,
% 3.70/3.88      (![X19 : $i, X20 : $i]:
% 3.70/3.88         (((X20) != (k6_relat_1 @ X19))
% 3.70/3.88          | ((k1_relat_1 @ X20) = (X19))
% 3.70/3.88          | ~ (v1_funct_1 @ X20)
% 3.70/3.88          | ~ (v1_relat_1 @ X20))),
% 3.70/3.88      inference('cnf', [status(esa)], [t34_funct_1])).
% 3.70/3.88  thf('19', plain,
% 3.70/3.88      (![X19 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ (k6_relat_1 @ X19))
% 3.70/3.88          | ~ (v1_funct_1 @ (k6_relat_1 @ X19))
% 3.70/3.88          | ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19)))),
% 3.70/3.88      inference('simplify', [status(thm)], ['18'])).
% 3.70/3.88  thf(fc3_funct_1, axiom,
% 3.70/3.88    (![A:$i]:
% 3.70/3.88     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.70/3.88       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.70/3.88  thf('20', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.70/3.88  thf('21', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 3.70/3.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.70/3.88  thf('22', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 3.70/3.88      inference('demod', [status(thm)], ['19', '20', '21'])).
% 3.70/3.88  thf('23', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X0)
% 3.70/3.88          | ~ (v1_relat_1 @ X1)
% 3.70/3.88          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 3.70/3.88              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 3.70/3.88      inference('simplify', [status(thm)], ['15'])).
% 3.70/3.88  thf('24', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.70/3.88            = (k1_relat_1 @ 
% 3.70/3.88               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.70/3.88      inference('sup+', [status(thm)], ['22', '23'])).
% 3.70/3.88  thf('25', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.70/3.88  thf('26', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.70/3.88            = (k1_relat_1 @ 
% 3.70/3.88               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1))),
% 3.70/3.88      inference('demod', [status(thm)], ['24', '25'])).
% 3.70/3.88  thf('27', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88            = (k1_relat_1 @ 
% 3.70/3.88               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ sk_A))))
% 3.70/3.88          | ~ (v1_relat_1 @ sk_B))),
% 3.70/3.88      inference('sup+', [status(thm)], ['17', '26'])).
% 3.70/3.88  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('29', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ 
% 3.70/3.88              (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ sk_A))))),
% 3.70/3.88      inference('demod', [status(thm)], ['27', '28'])).
% 3.70/3.88  thf('30', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88            = (k1_relat_1 @ 
% 3.70/3.88               (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 3.70/3.88          | ~ (v1_relat_1 @ sk_A)
% 3.70/3.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.70/3.88      inference('sup+', [status(thm)], ['16', '29'])).
% 3.70/3.88  thf('31', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 3.70/3.88      inference('demod', [status(thm)], ['19', '20', '21'])).
% 3.70/3.88  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('33', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.70/3.88  thf('34', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.70/3.88  thf('35', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.70/3.88  thf('36', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.70/3.88  thf('37', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ 
% 3.70/3.88              (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ sk_A))))),
% 3.70/3.88      inference('demod', [status(thm)], ['27', '28'])).
% 3.70/3.88  thf('38', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X0)
% 3.70/3.88          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 3.70/3.88              = (k7_relat_1 @ X1 @ 
% 3.70/3.88                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1))),
% 3.70/3.88      inference('cnf', [status(esa)], [t189_relat_1])).
% 3.70/3.88  thf('39', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (((k7_relat_1 @ sk_A @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 3.70/3.88            = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))
% 3.70/3.88          | ~ (v1_relat_1 @ sk_A)
% 3.70/3.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.70/3.88      inference('sup+', [status(thm)], ['37', '38'])).
% 3.70/3.88  thf('40', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 3.70/3.88      inference('demod', [status(thm)], ['19', '20', '21'])).
% 3.70/3.88  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('42', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.70/3.88  thf('43', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k7_relat_1 @ sk_A @ X0)
% 3.70/3.88           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))))),
% 3.70/3.88      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 3.70/3.88  thf('44', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.70/3.88  thf('45', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k7_relat_1 @ sk_A @ X0)
% 3.70/3.88           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 3.70/3.88      inference('demod', [status(thm)], ['43', '44'])).
% 3.70/3.88  thf('46', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.70/3.88  thf('47', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.70/3.88  thf('48', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_funct_1 @ X1)
% 3.70/3.88          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 3.70/3.88               (k1_relat_1 @ X1))
% 3.70/3.88          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 3.70/3.88              = (k7_relat_1 @ sk_A @ X0))
% 3.70/3.88          | (r2_hidden @ 
% 3.70/3.88             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ X1) @ 
% 3.70/3.88             (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 3.70/3.88      inference('demod', [status(thm)],
% 3.70/3.88                ['10', '34', '35', '36', '45', '46', '47'])).
% 3.70/3.88  thf('49', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 3.70/3.88             (k1_relat_1 @ sk_A))
% 3.70/3.88          | (r2_hidden @ 
% 3.70/3.88             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 3.70/3.88             (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 3.70/3.88          | ((k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 3.70/3.88              = (k7_relat_1 @ sk_A @ X0))
% 3.70/3.88          | ~ (v1_funct_1 @ sk_B)
% 3.70/3.88          | ~ (v1_relat_1 @ sk_B))),
% 3.70/3.88      inference('sup-', [status(thm)], ['0', '48'])).
% 3.70/3.88  thf('50', plain,
% 3.70/3.88      (![X7 : $i, X8 : $i]:
% 3.70/3.88         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X7 @ X8)) @ 
% 3.70/3.88           (k1_relat_1 @ X7))
% 3.70/3.88          | ~ (v1_relat_1 @ X7))),
% 3.70/3.88      inference('cnf', [status(esa)], [t89_relat_1])).
% 3.70/3.88  thf('51', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('52', plain,
% 3.70/3.88      (![X9 : $i, X10 : $i]:
% 3.70/3.88         (~ (r1_tarski @ X9 @ (k1_relat_1 @ X10))
% 3.70/3.88          | ((k1_relat_1 @ (k7_relat_1 @ X10 @ X9)) = (X9))
% 3.70/3.88          | ~ (v1_relat_1 @ X10))),
% 3.70/3.88      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.70/3.88  thf('53', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 3.70/3.88          | ~ (v1_relat_1 @ sk_B)
% 3.70/3.88          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) = (X0)))),
% 3.70/3.88      inference('sup-', [status(thm)], ['51', '52'])).
% 3.70/3.88  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('55', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 3.70/3.88          | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) = (X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['53', '54'])).
% 3.70/3.88  thf('56', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ sk_A)
% 3.70/3.88          | ((k1_relat_1 @ 
% 3.70/3.88              (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 3.70/3.88              = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 3.70/3.88      inference('sup-', [status(thm)], ['50', '55'])).
% 3.70/3.88  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('58', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ 
% 3.70/3.88           (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['56', '57'])).
% 3.70/3.88  thf('59', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 3.70/3.88          (k1_relat_1 @ sk_A))),
% 3.70/3.88      inference('demod', [status(thm)], ['3', '4'])).
% 3.70/3.88  thf('60', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 3.70/3.88          (k1_relat_1 @ sk_A))),
% 3.70/3.88      inference('sup+', [status(thm)], ['58', '59'])).
% 3.70/3.88  thf('61', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.70/3.88  thf('62', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.70/3.88            = (k1_relat_1 @ 
% 3.70/3.88               (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1))),
% 3.70/3.88      inference('demod', [status(thm)], ['24', '25'])).
% 3.70/3.88  thf('63', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X0)
% 3.70/3.88          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ X0))
% 3.70/3.88              = (k7_relat_1 @ X1 @ 
% 3.70/3.88                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1))),
% 3.70/3.88      inference('cnf', [status(esa)], [t189_relat_1])).
% 3.70/3.88  thf('64', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (((k7_relat_1 @ X1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 3.70/3.88            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.70/3.88      inference('sup+', [status(thm)], ['62', '63'])).
% 3.70/3.88  thf('65', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 3.70/3.88      inference('demod', [status(thm)], ['19', '20', '21'])).
% 3.70/3.88  thf('66', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.70/3.88  thf('67', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (((k7_relat_1 @ X1 @ X0)
% 3.70/3.88            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.70/3.88          | ~ (v1_relat_1 @ X1)
% 3.70/3.88          | ~ (v1_relat_1 @ X1))),
% 3.70/3.88      inference('demod', [status(thm)], ['64', '65', '66'])).
% 3.70/3.88  thf('68', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X1)
% 3.70/3.88          | ((k7_relat_1 @ X1 @ X0)
% 3.70/3.88              = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 3.70/3.88      inference('simplify', [status(thm)], ['67'])).
% 3.70/3.88  thf('69', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (((k7_relat_1 @ sk_B @ X0)
% 3.70/3.88            = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))
% 3.70/3.88          | ~ (v1_relat_1 @ sk_B))),
% 3.70/3.88      inference('sup+', [status(thm)], ['61', '68'])).
% 3.70/3.88  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('71', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k7_relat_1 @ sk_B @ X0)
% 3.70/3.88           = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 3.70/3.88      inference('demod', [status(thm)], ['69', '70'])).
% 3.70/3.88  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('74', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((r2_hidden @ 
% 3.70/3.88           (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 3.70/3.88           (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 3.70/3.88          | ((k7_relat_1 @ sk_B @ X0) = (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['49', '60', '71', '72', '73'])).
% 3.70/3.88  thf('75', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ 
% 3.70/3.88              (k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ sk_A))))),
% 3.70/3.88      inference('demod', [status(thm)], ['27', '28'])).
% 3.70/3.88  thf(t86_relat_1, axiom,
% 3.70/3.88    (![A:$i,B:$i,C:$i]:
% 3.70/3.88     ( ( v1_relat_1 @ C ) =>
% 3.70/3.88       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 3.70/3.88         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 3.70/3.88  thf('76', plain,
% 3.70/3.88      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.70/3.88         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X4 @ X3)))
% 3.70/3.88          | (r2_hidden @ X2 @ (k1_relat_1 @ X4))
% 3.70/3.88          | ~ (v1_relat_1 @ X4))),
% 3.70/3.88      inference('cnf', [status(esa)], [t86_relat_1])).
% 3.70/3.88  thf('77', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 3.70/3.88          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.70/3.88          | (r2_hidden @ X1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 3.70/3.88      inference('sup-', [status(thm)], ['75', '76'])).
% 3.70/3.88  thf('78', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.88      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.70/3.88  thf('79', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 3.70/3.88      inference('demod', [status(thm)], ['19', '20', '21'])).
% 3.70/3.88  thf('80', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 3.70/3.88          | (r2_hidden @ X1 @ X0))),
% 3.70/3.88      inference('demod', [status(thm)], ['77', '78', '79'])).
% 3.70/3.88  thf('81', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 3.70/3.88           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 3.70/3.88      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.70/3.88  thf('82', plain,
% 3.70/3.88      (![X0 : $i, X1 : $i]:
% 3.70/3.88         (~ (r2_hidden @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 3.70/3.88          | (r2_hidden @ X1 @ X0))),
% 3.70/3.88      inference('demod', [status(thm)], ['80', '81'])).
% 3.70/3.88  thf('83', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (((k7_relat_1 @ sk_B @ X0) = (k7_relat_1 @ sk_A @ X0))
% 3.70/3.88          | (r2_hidden @ 
% 3.70/3.88             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ sk_A @ sk_B) @ 
% 3.70/3.88             X0))),
% 3.70/3.88      inference('sup-', [status(thm)], ['74', '82'])).
% 3.70/3.88  thf('84', plain,
% 3.70/3.88      (![X22 : $i]:
% 3.70/3.88         (((k1_funct_1 @ sk_A @ X22) = (k1_funct_1 @ sk_B @ X22))
% 3.70/3.88          | ~ (r2_hidden @ X22 @ sk_C_1))),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('85', plain,
% 3.70/3.88      ((((k7_relat_1 @ sk_B @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1))
% 3.70/3.88        | ((k1_funct_1 @ sk_A @ 
% 3.70/3.88            (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B))
% 3.70/3.88            = (k1_funct_1 @ sk_B @ 
% 3.70/3.88               (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ 
% 3.70/3.88                sk_B))))),
% 3.70/3.88      inference('sup-', [status(thm)], ['83', '84'])).
% 3.70/3.88  thf('86', plain,
% 3.70/3.88      (((k7_relat_1 @ sk_A @ sk_C_1) != (k7_relat_1 @ sk_B @ sk_C_1))),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('87', plain,
% 3.70/3.88      (((k1_funct_1 @ sk_A @ 
% 3.70/3.88         (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B))
% 3.70/3.88         = (k1_funct_1 @ sk_B @ 
% 3.70/3.88            (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B)))),
% 3.70/3.88      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 3.70/3.88  thf('88', plain,
% 3.70/3.88      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.70/3.88         (~ (v1_relat_1 @ X15)
% 3.70/3.88          | ~ (v1_funct_1 @ X15)
% 3.70/3.88          | ((k1_funct_1 @ X17 @ (sk_D @ X16 @ X15 @ X17))
% 3.70/3.88              != (k1_funct_1 @ X15 @ (sk_D @ X16 @ X15 @ X17)))
% 3.70/3.88          | ((k7_relat_1 @ X17 @ X16) = (k7_relat_1 @ X15 @ X16))
% 3.70/3.88          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X15))
% 3.70/3.88          | ~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 3.70/3.88          | ~ (v1_funct_1 @ X17)
% 3.70/3.88          | ~ (v1_relat_1 @ X17))),
% 3.70/3.88      inference('cnf', [status(esa)], [t165_funct_1])).
% 3.70/3.88  thf('89', plain,
% 3.70/3.88      ((((k1_funct_1 @ sk_A @ 
% 3.70/3.88          (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B))
% 3.70/3.88          != (k1_funct_1 @ sk_A @ 
% 3.70/3.88              (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B)))
% 3.70/3.88        | ~ (v1_relat_1 @ sk_B)
% 3.70/3.88        | ~ (v1_funct_1 @ sk_B)
% 3.70/3.88        | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 3.70/3.88             (k1_relat_1 @ sk_B))
% 3.70/3.88        | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 3.70/3.88             (k1_relat_1 @ sk_A))
% 3.70/3.88        | ((k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)))
% 3.70/3.88            = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1))))
% 3.70/3.88        | ~ (v1_funct_1 @ sk_A)
% 3.70/3.88        | ~ (v1_relat_1 @ sk_A))),
% 3.70/3.88      inference('sup-', [status(thm)], ['87', '88'])).
% 3.70/3.88  thf('90', plain, ((v1_relat_1 @ sk_B)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('91', plain, ((v1_funct_1 @ sk_B)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('92', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('93', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 3.70/3.88          (k1_relat_1 @ sk_A))),
% 3.70/3.88      inference('sup+', [status(thm)], ['58', '59'])).
% 3.70/3.88  thf('94', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)) @ 
% 3.70/3.88          (k1_relat_1 @ sk_A))),
% 3.70/3.88      inference('sup+', [status(thm)], ['58', '59'])).
% 3.70/3.88  thf('95', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k7_relat_1 @ sk_B @ X0)
% 3.70/3.88           = (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 3.70/3.88      inference('demod', [status(thm)], ['69', '70'])).
% 3.70/3.88  thf('96', plain,
% 3.70/3.88      (![X0 : $i]:
% 3.70/3.88         ((k7_relat_1 @ sk_A @ X0)
% 3.70/3.88           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))))),
% 3.70/3.88      inference('demod', [status(thm)], ['43', '44'])).
% 3.70/3.88  thf('97', plain, ((v1_funct_1 @ sk_A)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('98', plain, ((v1_relat_1 @ sk_A)),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('99', plain,
% 3.70/3.88      ((((k1_funct_1 @ sk_A @ 
% 3.70/3.88          (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B))
% 3.70/3.88          != (k1_funct_1 @ sk_A @ 
% 3.70/3.88              (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ sk_A @ sk_B)))
% 3.70/3.88        | ((k7_relat_1 @ sk_B @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1)))),
% 3.70/3.88      inference('demod', [status(thm)],
% 3.70/3.88                ['89', '90', '91', '92', '93', '94', '95', '96', '97', '98'])).
% 3.70/3.88  thf('100', plain,
% 3.70/3.88      (((k7_relat_1 @ sk_B @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1))),
% 3.70/3.88      inference('simplify', [status(thm)], ['99'])).
% 3.70/3.88  thf('101', plain,
% 3.70/3.88      (((k7_relat_1 @ sk_A @ sk_C_1) != (k7_relat_1 @ sk_B @ sk_C_1))),
% 3.70/3.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.88  thf('102', plain, ($false),
% 3.70/3.88      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 3.70/3.88  
% 3.70/3.88  % SZS output end Refutation
% 3.70/3.88  
% 3.70/3.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
