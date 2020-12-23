%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yLVHx4Gf7y

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:13 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 295 expanded)
%              Number of leaves         :   18 (  94 expanded)
%              Depth                    :   24
%              Number of atoms          :  913 (4941 expanded)
%              Number of equality atoms :   56 ( 440 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

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

thf('1',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('3',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','19'])).

thf('21',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( sk_D @ X10 @ X9 @ X11 ) @ X10 )
      | ( ( k7_relat_1 @ X11 @ X10 )
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X4 @ X3 ) ) )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X13: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X13 )
        = ( k1_funct_1 @ sk_B @ X13 ) )
      | ~ ( r2_hidden @ X13 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ X11 @ ( sk_D @ X10 @ X9 @ X11 ) )
       != ( k1_funct_1 @ X9 @ ( sk_D @ X10 @ X9 @ X11 ) ) )
      | ( ( k7_relat_1 @ X11 @ X10 )
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) ) )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('58',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) ) )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56','57','58','59'])).

thf('61',plain,
    ( ( k7_relat_1 @ sk_B @ sk_C )
    = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k7_relat_1 @ sk_B @ sk_C )
    = ( k7_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yLVHx4Gf7y
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:23:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.35/1.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.61  % Solved by: fo/fo7.sh
% 1.35/1.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.61  % done 901 iterations in 1.164s
% 1.35/1.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.61  % SZS output start Refutation
% 1.35/1.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.35/1.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.61  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.61  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.35/1.61  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.61  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.35/1.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.35/1.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.61  thf(t192_relat_1, axiom,
% 1.35/1.61    (![A:$i,B:$i]:
% 1.35/1.61     ( ( v1_relat_1 @ B ) =>
% 1.35/1.61       ( ( k7_relat_1 @ B @ A ) =
% 1.35/1.61         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 1.35/1.61  thf('0', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (((k7_relat_1 @ X0 @ X1)
% 1.35/1.61            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 1.35/1.61          | ~ (v1_relat_1 @ X0))),
% 1.35/1.61      inference('cnf', [status(esa)], [t192_relat_1])).
% 1.35/1.61  thf(t166_funct_1, conjecture,
% 1.35/1.61    (![A:$i]:
% 1.35/1.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.61       ( ![B:$i]:
% 1.35/1.61         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.61           ( ![C:$i]:
% 1.35/1.61             ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.35/1.61                 ( ![D:$i]:
% 1.35/1.61                   ( ( r2_hidden @ D @ C ) =>
% 1.35/1.61                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 1.35/1.61               ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ))).
% 1.35/1.61  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.61    (~( ![A:$i]:
% 1.35/1.61        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.61          ( ![B:$i]:
% 1.35/1.61            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.61              ( ![C:$i]:
% 1.35/1.61                ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.35/1.61                    ( ![D:$i]:
% 1.35/1.61                      ( ( r2_hidden @ D @ C ) =>
% 1.35/1.61                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 1.35/1.61                  ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ) )),
% 1.35/1.61    inference('cnf.neg', [status(esa)], [t166_funct_1])).
% 1.35/1.61  thf('1', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf(t90_relat_1, axiom,
% 1.35/1.61    (![A:$i,B:$i]:
% 1.35/1.61     ( ( v1_relat_1 @ B ) =>
% 1.35/1.61       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.35/1.61         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.35/1.61  thf('2', plain,
% 1.35/1.61      (![X7 : $i, X8 : $i]:
% 1.35/1.61         (((k1_relat_1 @ (k7_relat_1 @ X7 @ X8))
% 1.35/1.61            = (k3_xboole_0 @ (k1_relat_1 @ X7) @ X8))
% 1.35/1.61          | ~ (v1_relat_1 @ X7))),
% 1.35/1.61      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.35/1.61  thf('3', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('4', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (((k7_relat_1 @ X0 @ X1)
% 1.35/1.61            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 1.35/1.61          | ~ (v1_relat_1 @ X0))),
% 1.35/1.61      inference('cnf', [status(esa)], [t192_relat_1])).
% 1.35/1.61  thf('5', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (((k7_relat_1 @ sk_B @ X0)
% 1.35/1.61            = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.35/1.61          | ~ (v1_relat_1 @ sk_B))),
% 1.35/1.61      inference('sup+', [status(thm)], ['3', '4'])).
% 1.35/1.61  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('7', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         ((k7_relat_1 @ sk_B @ X0)
% 1.35/1.61           = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.35/1.61      inference('demod', [status(thm)], ['5', '6'])).
% 1.35/1.61  thf('8', plain,
% 1.35/1.61      (![X7 : $i, X8 : $i]:
% 1.35/1.61         (((k1_relat_1 @ (k7_relat_1 @ X7 @ X8))
% 1.35/1.61            = (k3_xboole_0 @ (k1_relat_1 @ X7) @ X8))
% 1.35/1.61          | ~ (v1_relat_1 @ X7))),
% 1.35/1.61      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.35/1.61  thf('9', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.35/1.61            = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 1.35/1.61               (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.35/1.61          | ~ (v1_relat_1 @ sk_B))),
% 1.35/1.61      inference('sup+', [status(thm)], ['7', '8'])).
% 1.35/1.61  thf('10', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('12', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.35/1.61           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 1.35/1.61              (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.35/1.61      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.35/1.61  thf('13', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (((k7_relat_1 @ X0 @ X1)
% 1.35/1.61            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 1.35/1.61          | ~ (v1_relat_1 @ X0))),
% 1.35/1.61      inference('cnf', [status(esa)], [t192_relat_1])).
% 1.35/1.61  thf('14', plain,
% 1.35/1.61      (![X7 : $i, X8 : $i]:
% 1.35/1.61         (((k1_relat_1 @ (k7_relat_1 @ X7 @ X8))
% 1.35/1.61            = (k3_xboole_0 @ (k1_relat_1 @ X7) @ X8))
% 1.35/1.61          | ~ (v1_relat_1 @ X7))),
% 1.35/1.61      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.35/1.61  thf('15', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.35/1.61            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.35/1.61               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 1.35/1.61          | ~ (v1_relat_1 @ X1)
% 1.35/1.61          | ~ (v1_relat_1 @ X1))),
% 1.35/1.61      inference('sup+', [status(thm)], ['13', '14'])).
% 1.35/1.61  thf('16', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (~ (v1_relat_1 @ X1)
% 1.35/1.61          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.35/1.61              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.35/1.61                 (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 1.35/1.61      inference('simplify', [status(thm)], ['15'])).
% 1.35/1.61  thf('17', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 1.35/1.61            = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 1.35/1.61          | ~ (v1_relat_1 @ sk_A))),
% 1.35/1.61      inference('sup+', [status(thm)], ['12', '16'])).
% 1.35/1.61  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('19', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 1.35/1.61           = (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 1.35/1.61      inference('demod', [status(thm)], ['17', '18'])).
% 1.35/1.61  thf('20', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 1.35/1.61            = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))
% 1.35/1.61          | ~ (v1_relat_1 @ sk_B))),
% 1.35/1.61      inference('sup+', [status(thm)], ['2', '19'])).
% 1.35/1.61  thf('21', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('23', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 1.35/1.61           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))),
% 1.35/1.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.35/1.61  thf(t89_relat_1, axiom,
% 1.35/1.61    (![A:$i,B:$i]:
% 1.35/1.61     ( ( v1_relat_1 @ B ) =>
% 1.35/1.61       ( r1_tarski @
% 1.35/1.61         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 1.35/1.61  thf('24', plain,
% 1.35/1.61      (![X5 : $i, X6 : $i]:
% 1.35/1.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X5 @ X6)) @ 
% 1.35/1.61           (k1_relat_1 @ X5))
% 1.35/1.61          | ~ (v1_relat_1 @ X5))),
% 1.35/1.61      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.35/1.61  thf('25', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.35/1.61           (k1_relat_1 @ sk_A))
% 1.35/1.61          | ~ (v1_relat_1 @ sk_A))),
% 1.35/1.61      inference('sup+', [status(thm)], ['23', '24'])).
% 1.35/1.61  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('27', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.35/1.61          (k1_relat_1 @ sk_A))),
% 1.35/1.61      inference('demod', [status(thm)], ['25', '26'])).
% 1.35/1.61  thf(t165_funct_1, axiom,
% 1.35/1.61    (![A:$i]:
% 1.35/1.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.61       ( ![B:$i]:
% 1.35/1.61         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.35/1.61           ( ![C:$i]:
% 1.35/1.61             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 1.35/1.61                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 1.35/1.61               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 1.35/1.61                 ( ![D:$i]:
% 1.35/1.61                   ( ( r2_hidden @ D @ C ) =>
% 1.35/1.61                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 1.35/1.61  thf('28', plain,
% 1.35/1.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.35/1.61         (~ (v1_relat_1 @ X9)
% 1.35/1.61          | ~ (v1_funct_1 @ X9)
% 1.35/1.61          | (r2_hidden @ (sk_D @ X10 @ X9 @ X11) @ X10)
% 1.35/1.61          | ((k7_relat_1 @ X11 @ X10) = (k7_relat_1 @ X9 @ X10))
% 1.35/1.61          | ~ (r1_tarski @ X10 @ (k1_relat_1 @ X9))
% 1.35/1.61          | ~ (r1_tarski @ X10 @ (k1_relat_1 @ X11))
% 1.35/1.61          | ~ (v1_funct_1 @ X11)
% 1.35/1.61          | ~ (v1_relat_1 @ X11))),
% 1.35/1.61      inference('cnf', [status(esa)], [t165_funct_1])).
% 1.35/1.61  thf('29', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (~ (v1_relat_1 @ X1)
% 1.35/1.61          | ~ (v1_funct_1 @ X1)
% 1.35/1.61          | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.35/1.61               (k1_relat_1 @ X1))
% 1.35/1.61          | ((k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.35/1.61              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.35/1.61          | (r2_hidden @ 
% 1.35/1.61             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ X1) @ 
% 1.35/1.61             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.35/1.61          | ~ (v1_funct_1 @ sk_A)
% 1.35/1.61          | ~ (v1_relat_1 @ sk_A))),
% 1.35/1.61      inference('sup-', [status(thm)], ['27', '28'])).
% 1.35/1.61  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('32', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (~ (v1_relat_1 @ X1)
% 1.35/1.61          | ~ (v1_funct_1 @ X1)
% 1.35/1.61          | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.35/1.61               (k1_relat_1 @ X1))
% 1.35/1.61          | ((k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.35/1.61              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.35/1.61          | (r2_hidden @ 
% 1.35/1.61             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ X1) @ 
% 1.35/1.61             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.35/1.61      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.35/1.61  thf('33', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.35/1.61             (k1_relat_1 @ sk_A))
% 1.35/1.61          | (r2_hidden @ 
% 1.35/1.61             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B) @ 
% 1.35/1.61             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.35/1.61          | ((k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.35/1.61              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.35/1.61          | ~ (v1_funct_1 @ sk_B)
% 1.35/1.61          | ~ (v1_relat_1 @ sk_B))),
% 1.35/1.61      inference('sup-', [status(thm)], ['1', '32'])).
% 1.35/1.61  thf('34', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.35/1.61          (k1_relat_1 @ sk_A))),
% 1.35/1.61      inference('demod', [status(thm)], ['25', '26'])).
% 1.35/1.61  thf('35', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         ((k7_relat_1 @ sk_B @ X0)
% 1.35/1.61           = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.35/1.61      inference('demod', [status(thm)], ['5', '6'])).
% 1.35/1.61  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('38', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         ((r2_hidden @ 
% 1.35/1.61           (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B) @ 
% 1.35/1.61           (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.35/1.61          | ((k7_relat_1 @ sk_B @ X0)
% 1.35/1.61              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))))),
% 1.35/1.61      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 1.35/1.61  thf('39', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('40', plain,
% 1.35/1.61      (![X7 : $i, X8 : $i]:
% 1.35/1.61         (((k1_relat_1 @ (k7_relat_1 @ X7 @ X8))
% 1.35/1.61            = (k3_xboole_0 @ (k1_relat_1 @ X7) @ X8))
% 1.35/1.61          | ~ (v1_relat_1 @ X7))),
% 1.35/1.61      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.35/1.61  thf(t86_relat_1, axiom,
% 1.35/1.61    (![A:$i,B:$i,C:$i]:
% 1.35/1.61     ( ( v1_relat_1 @ C ) =>
% 1.35/1.61       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 1.35/1.61         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 1.35/1.61  thf('41', plain,
% 1.35/1.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.35/1.61         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X4 @ X3)))
% 1.35/1.61          | (r2_hidden @ X2 @ X3)
% 1.35/1.61          | ~ (v1_relat_1 @ X4))),
% 1.35/1.61      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.35/1.61  thf('42', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.61         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 1.35/1.61          | ~ (v1_relat_1 @ X1)
% 1.35/1.61          | ~ (v1_relat_1 @ X1)
% 1.35/1.61          | (r2_hidden @ X2 @ X0))),
% 1.35/1.61      inference('sup-', [status(thm)], ['40', '41'])).
% 1.35/1.61  thf('43', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.61         ((r2_hidden @ X2 @ X0)
% 1.35/1.61          | ~ (v1_relat_1 @ X1)
% 1.35/1.61          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 1.35/1.61      inference('simplify', [status(thm)], ['42'])).
% 1.35/1.61  thf('44', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.35/1.61          | ~ (v1_relat_1 @ sk_B)
% 1.35/1.61          | (r2_hidden @ X1 @ X0))),
% 1.35/1.61      inference('sup-', [status(thm)], ['39', '43'])).
% 1.35/1.61  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('46', plain,
% 1.35/1.61      (![X0 : $i, X1 : $i]:
% 1.35/1.61         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.35/1.61          | (r2_hidden @ X1 @ X0))),
% 1.35/1.61      inference('demod', [status(thm)], ['44', '45'])).
% 1.35/1.61  thf('47', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (((k7_relat_1 @ sk_B @ X0)
% 1.35/1.61            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.35/1.61          | (r2_hidden @ 
% 1.35/1.61             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B) @ 
% 1.35/1.61             X0))),
% 1.35/1.61      inference('sup-', [status(thm)], ['38', '46'])).
% 1.35/1.61  thf('48', plain,
% 1.35/1.61      (![X13 : $i]:
% 1.35/1.61         (((k1_funct_1 @ sk_A @ X13) = (k1_funct_1 @ sk_B @ X13))
% 1.35/1.61          | ~ (r2_hidden @ X13 @ sk_C))),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('49', plain,
% 1.35/1.61      ((((k7_relat_1 @ sk_B @ sk_C)
% 1.35/1.61          = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C)))
% 1.35/1.61        | ((k1_funct_1 @ sk_A @ 
% 1.35/1.61            (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))
% 1.35/1.61            = (k1_funct_1 @ sk_B @ 
% 1.35/1.61               (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))))),
% 1.35/1.61      inference('sup-', [status(thm)], ['47', '48'])).
% 1.35/1.61  thf('50', plain,
% 1.35/1.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.35/1.61         (~ (v1_relat_1 @ X9)
% 1.35/1.61          | ~ (v1_funct_1 @ X9)
% 1.35/1.61          | ((k1_funct_1 @ X11 @ (sk_D @ X10 @ X9 @ X11))
% 1.35/1.61              != (k1_funct_1 @ X9 @ (sk_D @ X10 @ X9 @ X11)))
% 1.35/1.61          | ((k7_relat_1 @ X11 @ X10) = (k7_relat_1 @ X9 @ X10))
% 1.35/1.61          | ~ (r1_tarski @ X10 @ (k1_relat_1 @ X9))
% 1.35/1.61          | ~ (r1_tarski @ X10 @ (k1_relat_1 @ X11))
% 1.35/1.61          | ~ (v1_funct_1 @ X11)
% 1.35/1.61          | ~ (v1_relat_1 @ X11))),
% 1.35/1.61      inference('cnf', [status(esa)], [t165_funct_1])).
% 1.35/1.61  thf('51', plain,
% 1.35/1.61      ((((k1_funct_1 @ sk_A @ 
% 1.35/1.61          (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))
% 1.35/1.61          != (k1_funct_1 @ sk_A @ 
% 1.35/1.61              (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B)))
% 1.35/1.61        | ((k7_relat_1 @ sk_B @ sk_C)
% 1.35/1.61            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C)))
% 1.35/1.61        | ~ (v1_relat_1 @ sk_B)
% 1.35/1.61        | ~ (v1_funct_1 @ sk_B)
% 1.35/1.61        | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ 
% 1.35/1.61             (k1_relat_1 @ sk_B))
% 1.35/1.61        | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ 
% 1.35/1.61             (k1_relat_1 @ sk_A))
% 1.35/1.61        | ((k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C))
% 1.35/1.61            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C)))
% 1.35/1.61        | ~ (v1_funct_1 @ sk_A)
% 1.35/1.61        | ~ (v1_relat_1 @ sk_A))),
% 1.35/1.61      inference('sup-', [status(thm)], ['49', '50'])).
% 1.35/1.61  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('54', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('55', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.35/1.61          (k1_relat_1 @ sk_A))),
% 1.35/1.61      inference('demod', [status(thm)], ['25', '26'])).
% 1.35/1.61  thf('56', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.35/1.61          (k1_relat_1 @ sk_A))),
% 1.35/1.61      inference('demod', [status(thm)], ['25', '26'])).
% 1.35/1.61  thf('57', plain,
% 1.35/1.61      (![X0 : $i]:
% 1.35/1.61         ((k7_relat_1 @ sk_B @ X0)
% 1.35/1.61           = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.35/1.61      inference('demod', [status(thm)], ['5', '6'])).
% 1.35/1.61  thf('58', plain, ((v1_funct_1 @ sk_A)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('60', plain,
% 1.35/1.61      ((((k1_funct_1 @ sk_A @ 
% 1.35/1.61          (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))
% 1.35/1.61          != (k1_funct_1 @ sk_A @ 
% 1.35/1.61              (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B)))
% 1.35/1.61        | ((k7_relat_1 @ sk_B @ sk_C)
% 1.35/1.61            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C)))
% 1.35/1.61        | ((k7_relat_1 @ sk_B @ sk_C)
% 1.35/1.61            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C))))),
% 1.35/1.61      inference('demod', [status(thm)],
% 1.35/1.61                ['51', '52', '53', '54', '55', '56', '57', '58', '59'])).
% 1.35/1.61  thf('61', plain,
% 1.35/1.61      (((k7_relat_1 @ sk_B @ sk_C)
% 1.35/1.61         = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C)))),
% 1.35/1.61      inference('simplify', [status(thm)], ['60'])).
% 1.35/1.61  thf('62', plain,
% 1.35/1.61      ((((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 1.35/1.61        | ~ (v1_relat_1 @ sk_A))),
% 1.35/1.61      inference('sup+', [status(thm)], ['0', '61'])).
% 1.35/1.61  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('64', plain, (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))),
% 1.35/1.61      inference('demod', [status(thm)], ['62', '63'])).
% 1.35/1.61  thf('65', plain,
% 1.35/1.61      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 1.35/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.61  thf('66', plain, ($false),
% 1.35/1.61      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 1.35/1.61  
% 1.35/1.61  % SZS output end Refutation
% 1.35/1.61  
% 1.45/1.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
