%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wrYT2Cfsaa

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:13 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 581 expanded)
%              Number of leaves         :   19 ( 171 expanded)
%              Depth                    :   25
%              Number of atoms          : 1179 (9142 expanded)
%              Number of equality atoms :   80 ( 835 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','28'])).

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

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r2_hidden @ ( sk_D @ X14 @ X13 @ X15 ) @ X14 )
      | ( ( k7_relat_1 @ X15 @ X14 )
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('38',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('48',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) ) @ X0 )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) ) @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ X0 )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','28'])).

thf('60',plain,
    ( ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('61',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','64','65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ ( k7_relat_1 @ X7 @ X6 ) ) )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,(
    ! [X17: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X17 )
        = ( k1_funct_1 @ sk_B @ X17 ) )
      | ~ ( r2_hidden @ X17 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ X15 @ ( sk_D @ X14 @ X13 @ X15 ) )
       != ( k1_funct_1 @ X13 @ ( sk_D @ X14 @ X13 @ X15 ) ) )
      | ( ( k7_relat_1 @ X15 @ X14 )
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('82',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','28'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','28'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('90',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) ) )
    | ( ( k7_relat_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88','89','90','91'])).

thf('93',plain,
    ( ( k7_relat_1 @ sk_B @ sk_C )
    = ( k7_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wrYT2Cfsaa
% 0.13/0.37  % Computer   : n017.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:24:31 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 1.44/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.44/1.64  % Solved by: fo/fo7.sh
% 1.44/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.64  % done 1299 iterations in 1.162s
% 1.44/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.44/1.64  % SZS output start Refutation
% 1.44/1.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.44/1.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.44/1.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.44/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.64  thf(sk_C_type, type, sk_C: $i).
% 1.44/1.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.44/1.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.44/1.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.44/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.44/1.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.44/1.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.44/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.44/1.64  thf(t166_funct_1, conjecture,
% 1.44/1.64    (![A:$i]:
% 1.44/1.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.44/1.64       ( ![B:$i]:
% 1.44/1.64         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.44/1.64           ( ![C:$i]:
% 1.44/1.64             ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.44/1.64                 ( ![D:$i]:
% 1.44/1.64                   ( ( r2_hidden @ D @ C ) =>
% 1.44/1.64                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 1.44/1.64               ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ))).
% 1.44/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.64    (~( ![A:$i]:
% 1.44/1.64        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.44/1.64          ( ![B:$i]:
% 1.44/1.64            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.44/1.64              ( ![C:$i]:
% 1.44/1.64                ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.44/1.64                    ( ![D:$i]:
% 1.44/1.64                      ( ( r2_hidden @ D @ C ) =>
% 1.44/1.64                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 1.44/1.64                  ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ) )),
% 1.44/1.64    inference('cnf.neg', [status(esa)], [t166_funct_1])).
% 1.44/1.64  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('1', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf(t89_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ B ) =>
% 1.44/1.64       ( r1_tarski @
% 1.44/1.64         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 1.44/1.64  thf('2', plain,
% 1.44/1.64      (![X8 : $i, X9 : $i]:
% 1.44/1.64         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ 
% 1.44/1.64           (k1_relat_1 @ X8))
% 1.44/1.64          | ~ (v1_relat_1 @ X8))),
% 1.44/1.64      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.44/1.64  thf('3', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 1.44/1.64           (k1_relat_1 @ sk_A))
% 1.44/1.64          | ~ (v1_relat_1 @ sk_B))),
% 1.44/1.64      inference('sup+', [status(thm)], ['1', '2'])).
% 1.44/1.64  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('5', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 1.44/1.64          (k1_relat_1 @ sk_A))),
% 1.44/1.64      inference('demod', [status(thm)], ['3', '4'])).
% 1.44/1.64  thf(t98_relat_1, axiom,
% 1.44/1.64    (![A:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ A ) =>
% 1.44/1.64       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 1.44/1.64  thf('6', plain,
% 1.44/1.64      (![X12 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (X12))
% 1.44/1.64          | ~ (v1_relat_1 @ X12))),
% 1.44/1.64      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.44/1.64  thf(t100_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i,C:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ C ) =>
% 1.44/1.64       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.44/1.64         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 1.44/1.64  thf('7', plain,
% 1.44/1.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X3) @ X4)
% 1.44/1.64            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 1.44/1.64          | ~ (v1_relat_1 @ X2))),
% 1.44/1.64      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.44/1.64  thf('8', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X0 @ X1)
% 1.44/1.64            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 1.44/1.64          | ~ (v1_relat_1 @ X0)
% 1.44/1.64          | ~ (v1_relat_1 @ X0))),
% 1.44/1.64      inference('sup+', [status(thm)], ['6', '7'])).
% 1.44/1.64  thf('9', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X0)
% 1.44/1.64          | ((k7_relat_1 @ X0 @ X1)
% 1.44/1.64              = (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 1.44/1.64      inference('simplify', [status(thm)], ['8'])).
% 1.44/1.64  thf(t90_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ B ) =>
% 1.44/1.64       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.44/1.64         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.44/1.64  thf('10', plain,
% 1.44/1.64      (![X10 : $i, X11 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X10 @ X11))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11))
% 1.44/1.64          | ~ (v1_relat_1 @ X10))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf('11', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.44/1.64               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ X1))),
% 1.44/1.64      inference('sup+', [status(thm)], ['9', '10'])).
% 1.44/1.64  thf('12', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.44/1.64              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.44/1.64                 (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 1.44/1.64      inference('simplify', [status(thm)], ['11'])).
% 1.44/1.64  thf('13', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('14', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.44/1.64              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.44/1.64                 (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 1.44/1.64      inference('simplify', [status(thm)], ['11'])).
% 1.44/1.64  thf('15', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 1.44/1.64               (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ sk_B))),
% 1.44/1.64      inference('sup+', [status(thm)], ['13', '14'])).
% 1.44/1.64  thf('16', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('18', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.44/1.64           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 1.44/1.64              (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.44/1.64  thf('19', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.44/1.64            = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ sk_A))),
% 1.44/1.64      inference('sup+', [status(thm)], ['12', '18'])).
% 1.44/1.64  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('21', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.44/1.64           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['19', '20'])).
% 1.44/1.64  thf('22', plain,
% 1.44/1.64      (![X10 : $i, X11 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X10 @ X11))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11))
% 1.44/1.64          | ~ (v1_relat_1 @ X10))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf('23', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.44/1.64           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['19', '20'])).
% 1.44/1.64  thf('24', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 1.44/1.64            = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ sk_B))),
% 1.44/1.64      inference('sup+', [status(thm)], ['22', '23'])).
% 1.44/1.64  thf('25', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('27', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 1.44/1.64           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.44/1.64  thf('28', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 1.44/1.64           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['21', '27'])).
% 1.44/1.64  thf('29', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.44/1.64          (k1_relat_1 @ sk_A))),
% 1.44/1.64      inference('demod', [status(thm)], ['5', '28'])).
% 1.44/1.64  thf(t165_funct_1, axiom,
% 1.44/1.64    (![A:$i]:
% 1.44/1.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.44/1.64       ( ![B:$i]:
% 1.44/1.64         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.44/1.64           ( ![C:$i]:
% 1.44/1.64             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 1.44/1.64                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 1.44/1.64               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 1.44/1.64                 ( ![D:$i]:
% 1.44/1.64                   ( ( r2_hidden @ D @ C ) =>
% 1.44/1.64                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 1.44/1.64  thf('30', plain,
% 1.44/1.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X13)
% 1.44/1.64          | ~ (v1_funct_1 @ X13)
% 1.44/1.64          | (r2_hidden @ (sk_D @ X14 @ X13 @ X15) @ X14)
% 1.44/1.64          | ((k7_relat_1 @ X15 @ X14) = (k7_relat_1 @ X13 @ X14))
% 1.44/1.64          | ~ (r1_tarski @ X14 @ (k1_relat_1 @ X13))
% 1.44/1.64          | ~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 1.44/1.64          | ~ (v1_funct_1 @ X15)
% 1.44/1.64          | ~ (v1_relat_1 @ X15))),
% 1.44/1.64      inference('cnf', [status(esa)], [t165_funct_1])).
% 1.44/1.64  thf('31', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_funct_1 @ X1)
% 1.44/1.64          | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.44/1.64               (k1_relat_1 @ X1))
% 1.44/1.64          | ((k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.44/1.64          | (r2_hidden @ 
% 1.44/1.64             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ X1) @ 
% 1.44/1.64             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64          | ~ (v1_funct_1 @ sk_A)
% 1.44/1.64          | ~ (v1_relat_1 @ sk_A))),
% 1.44/1.64      inference('sup-', [status(thm)], ['29', '30'])).
% 1.44/1.64  thf('32', plain, ((v1_funct_1 @ sk_A)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('34', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_funct_1 @ X1)
% 1.44/1.64          | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.44/1.64               (k1_relat_1 @ X1))
% 1.44/1.64          | ((k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.44/1.64          | (r2_hidden @ 
% 1.44/1.64             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ X1) @ 
% 1.44/1.64             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.44/1.64  thf('35', plain,
% 1.44/1.64      (![X12 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (X12))
% 1.44/1.64          | ~ (v1_relat_1 @ X12))),
% 1.44/1.64      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.44/1.64  thf('36', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('37', plain,
% 1.44/1.64      (![X12 : $i]:
% 1.44/1.64         (((k7_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (X12))
% 1.44/1.64          | ~ (v1_relat_1 @ X12))),
% 1.44/1.64      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.44/1.64  thf('38', plain,
% 1.44/1.64      ((((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)) = (sk_B))
% 1.44/1.64        | ~ (v1_relat_1 @ sk_B))),
% 1.44/1.64      inference('sup+', [status(thm)], ['36', '37'])).
% 1.44/1.64  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('40', plain, (((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)) = (sk_B))),
% 1.44/1.64      inference('demod', [status(thm)], ['38', '39'])).
% 1.44/1.64  thf('41', plain,
% 1.44/1.64      (![X10 : $i, X11 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X10 @ X11))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11))
% 1.44/1.64          | ~ (v1_relat_1 @ X10))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf('42', plain,
% 1.44/1.64      ((((k1_relat_1 @ sk_B)
% 1.44/1.64          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))
% 1.44/1.64        | ~ (v1_relat_1 @ sk_B))),
% 1.44/1.64      inference('sup+', [status(thm)], ['40', '41'])).
% 1.44/1.64  thf('43', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('44', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('46', plain,
% 1.44/1.64      (((k1_relat_1 @ sk_A)
% 1.44/1.64         = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)))),
% 1.44/1.64      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 1.44/1.64  thf('47', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X0)
% 1.44/1.64          | ((k7_relat_1 @ X0 @ X1)
% 1.44/1.64              = (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 1.44/1.64      inference('simplify', [status(thm)], ['8'])).
% 1.44/1.64  thf('48', plain,
% 1.44/1.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X3) @ X4)
% 1.44/1.64            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 1.44/1.64          | ~ (v1_relat_1 @ X2))),
% 1.44/1.64      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.44/1.64  thf('49', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64            = (k7_relat_1 @ X1 @ 
% 1.44/1.64               (k3_xboole_0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ X1))),
% 1.44/1.64      inference('sup+', [status(thm)], ['47', '48'])).
% 1.44/1.64  thf('50', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.44/1.64              = (k7_relat_1 @ X1 @ 
% 1.44/1.64                 (k3_xboole_0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2))))),
% 1.44/1.64      inference('simplify', [status(thm)], ['49'])).
% 1.44/1.64  thf('51', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) @ X0)
% 1.44/1.64            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ sk_A))),
% 1.44/1.64      inference('sup+', [status(thm)], ['46', '50'])).
% 1.44/1.64  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('53', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k7_relat_1 @ (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) @ X0)
% 1.44/1.64           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['51', '52'])).
% 1.44/1.64  thf('54', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k7_relat_1 @ sk_A @ X0)
% 1.44/1.64            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ sk_A))),
% 1.44/1.64      inference('sup+', [status(thm)], ['35', '53'])).
% 1.44/1.64  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('56', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k7_relat_1 @ sk_A @ X0)
% 1.44/1.64           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['54', '55'])).
% 1.44/1.64  thf('57', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_funct_1 @ X1)
% 1.44/1.64          | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.44/1.64               (k1_relat_1 @ X1))
% 1.44/1.64          | ((k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64              = (k7_relat_1 @ sk_A @ X0))
% 1.44/1.64          | (r2_hidden @ 
% 1.44/1.64             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ X1) @ 
% 1.44/1.64             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['34', '56'])).
% 1.44/1.64  thf('58', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.44/1.64             (k1_relat_1 @ sk_A))
% 1.44/1.64          | (r2_hidden @ 
% 1.44/1.64             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B) @ 
% 1.44/1.64             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64          | ((k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64              = (k7_relat_1 @ sk_A @ X0))
% 1.44/1.64          | ~ (v1_funct_1 @ sk_B)
% 1.44/1.64          | ~ (v1_relat_1 @ sk_B))),
% 1.44/1.64      inference('sup-', [status(thm)], ['0', '57'])).
% 1.44/1.64  thf('59', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.44/1.64          (k1_relat_1 @ sk_A))),
% 1.44/1.64      inference('demod', [status(thm)], ['5', '28'])).
% 1.44/1.64  thf('60', plain, (((k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)) = (sk_B))),
% 1.44/1.64      inference('demod', [status(thm)], ['38', '39'])).
% 1.44/1.64  thf('61', plain,
% 1.44/1.64      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.44/1.64         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X3) @ X4)
% 1.44/1.64            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 1.44/1.64          | ~ (v1_relat_1 @ X2))),
% 1.44/1.64      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.44/1.64  thf('62', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k7_relat_1 @ sk_B @ X0)
% 1.44/1.64            = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 1.44/1.64          | ~ (v1_relat_1 @ sk_B))),
% 1.44/1.64      inference('sup+', [status(thm)], ['60', '61'])).
% 1.44/1.64  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('64', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k7_relat_1 @ sk_B @ X0)
% 1.44/1.64           = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['62', '63'])).
% 1.44/1.64  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('67', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((r2_hidden @ 
% 1.44/1.64           (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B) @ 
% 1.44/1.64           (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64          | ((k7_relat_1 @ sk_B @ X0) = (k7_relat_1 @ sk_A @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['58', '59', '64', '65', '66'])).
% 1.44/1.64  thf('68', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('69', plain,
% 1.44/1.64      (![X10 : $i, X11 : $i]:
% 1.44/1.64         (((k1_relat_1 @ (k7_relat_1 @ X10 @ X11))
% 1.44/1.64            = (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11))
% 1.44/1.64          | ~ (v1_relat_1 @ X10))),
% 1.44/1.64      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.44/1.64  thf(t86_relat_1, axiom,
% 1.44/1.64    (![A:$i,B:$i,C:$i]:
% 1.44/1.64     ( ( v1_relat_1 @ C ) =>
% 1.44/1.64       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 1.44/1.64         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 1.44/1.64  thf('70', plain,
% 1.44/1.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.44/1.64         (~ (r2_hidden @ X5 @ (k1_relat_1 @ (k7_relat_1 @ X7 @ X6)))
% 1.44/1.64          | (r2_hidden @ X5 @ X6)
% 1.44/1.64          | ~ (v1_relat_1 @ X7))),
% 1.44/1.64      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.44/1.64  thf('71', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | (r2_hidden @ X2 @ X0))),
% 1.44/1.64      inference('sup-', [status(thm)], ['69', '70'])).
% 1.44/1.64  thf('72', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.64         ((r2_hidden @ X2 @ X0)
% 1.44/1.64          | ~ (v1_relat_1 @ X1)
% 1.44/1.64          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 1.44/1.64      inference('simplify', [status(thm)], ['71'])).
% 1.44/1.64  thf('73', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64          | ~ (v1_relat_1 @ sk_B)
% 1.44/1.64          | (r2_hidden @ X1 @ X0))),
% 1.44/1.64      inference('sup-', [status(thm)], ['68', '72'])).
% 1.44/1.64  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('75', plain,
% 1.44/1.64      (![X0 : $i, X1 : $i]:
% 1.44/1.64         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 1.44/1.64          | (r2_hidden @ X1 @ X0))),
% 1.44/1.64      inference('demod', [status(thm)], ['73', '74'])).
% 1.44/1.64  thf('76', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (((k7_relat_1 @ sk_B @ X0) = (k7_relat_1 @ sk_A @ X0))
% 1.44/1.64          | (r2_hidden @ 
% 1.44/1.64             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B) @ 
% 1.44/1.64             X0))),
% 1.44/1.64      inference('sup-', [status(thm)], ['67', '75'])).
% 1.44/1.64  thf('77', plain,
% 1.44/1.64      (![X17 : $i]:
% 1.44/1.64         (((k1_funct_1 @ sk_A @ X17) = (k1_funct_1 @ sk_B @ X17))
% 1.44/1.64          | ~ (r2_hidden @ X17 @ sk_C))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('78', plain,
% 1.44/1.64      ((((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))
% 1.44/1.64        | ((k1_funct_1 @ sk_A @ 
% 1.44/1.64            (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))
% 1.44/1.64            = (k1_funct_1 @ sk_B @ 
% 1.44/1.64               (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))))),
% 1.44/1.64      inference('sup-', [status(thm)], ['76', '77'])).
% 1.44/1.64  thf('79', plain,
% 1.44/1.64      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('80', plain,
% 1.44/1.64      (((k1_funct_1 @ sk_A @ 
% 1.44/1.64         (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))
% 1.44/1.64         = (k1_funct_1 @ sk_B @ 
% 1.44/1.64            (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B)))),
% 1.44/1.64      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 1.44/1.64  thf('81', plain,
% 1.44/1.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.44/1.64         (~ (v1_relat_1 @ X13)
% 1.44/1.64          | ~ (v1_funct_1 @ X13)
% 1.44/1.64          | ((k1_funct_1 @ X15 @ (sk_D @ X14 @ X13 @ X15))
% 1.44/1.64              != (k1_funct_1 @ X13 @ (sk_D @ X14 @ X13 @ X15)))
% 1.44/1.64          | ((k7_relat_1 @ X15 @ X14) = (k7_relat_1 @ X13 @ X14))
% 1.44/1.64          | ~ (r1_tarski @ X14 @ (k1_relat_1 @ X13))
% 1.44/1.64          | ~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 1.44/1.64          | ~ (v1_funct_1 @ X15)
% 1.44/1.64          | ~ (v1_relat_1 @ X15))),
% 1.44/1.64      inference('cnf', [status(esa)], [t165_funct_1])).
% 1.44/1.64  thf('82', plain,
% 1.44/1.64      ((((k1_funct_1 @ sk_A @ 
% 1.44/1.64          (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))
% 1.44/1.64          != (k1_funct_1 @ sk_A @ 
% 1.44/1.64              (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B)))
% 1.44/1.64        | ~ (v1_relat_1 @ sk_B)
% 1.44/1.64        | ~ (v1_funct_1 @ sk_B)
% 1.44/1.64        | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ 
% 1.44/1.64             (k1_relat_1 @ sk_B))
% 1.44/1.64        | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ 
% 1.44/1.64             (k1_relat_1 @ sk_A))
% 1.44/1.64        | ((k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C))
% 1.44/1.64            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C)))
% 1.44/1.64        | ~ (v1_funct_1 @ sk_A)
% 1.44/1.64        | ~ (v1_relat_1 @ sk_A))),
% 1.44/1.64      inference('sup-', [status(thm)], ['80', '81'])).
% 1.44/1.64  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('84', plain, ((v1_funct_1 @ sk_B)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('85', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('86', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.44/1.64          (k1_relat_1 @ sk_A))),
% 1.44/1.64      inference('demod', [status(thm)], ['5', '28'])).
% 1.44/1.64  thf('87', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.44/1.64          (k1_relat_1 @ sk_A))),
% 1.44/1.64      inference('demod', [status(thm)], ['5', '28'])).
% 1.44/1.64  thf('88', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k7_relat_1 @ sk_B @ X0)
% 1.44/1.64           = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['62', '63'])).
% 1.44/1.64  thf('89', plain,
% 1.44/1.64      (![X0 : $i]:
% 1.44/1.64         ((k7_relat_1 @ sk_A @ X0)
% 1.44/1.64           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 1.44/1.64      inference('demod', [status(thm)], ['54', '55'])).
% 1.44/1.64  thf('90', plain, ((v1_funct_1 @ sk_A)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('91', plain, ((v1_relat_1 @ sk_A)),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('92', plain,
% 1.44/1.64      ((((k1_funct_1 @ sk_A @ 
% 1.44/1.64          (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B))
% 1.44/1.64          != (k1_funct_1 @ sk_A @ 
% 1.44/1.64              (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C) @ sk_A @ sk_B)))
% 1.44/1.64        | ((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C)))),
% 1.44/1.64      inference('demod', [status(thm)],
% 1.44/1.64                ['82', '83', '84', '85', '86', '87', '88', '89', '90', '91'])).
% 1.44/1.64  thf('93', plain, (((k7_relat_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_A @ sk_C))),
% 1.44/1.64      inference('simplify', [status(thm)], ['92'])).
% 1.44/1.64  thf('94', plain,
% 1.44/1.64      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 1.44/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.64  thf('95', plain, ($false),
% 1.44/1.64      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 1.44/1.64  
% 1.44/1.64  % SZS output end Refutation
% 1.44/1.64  
% 1.44/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
