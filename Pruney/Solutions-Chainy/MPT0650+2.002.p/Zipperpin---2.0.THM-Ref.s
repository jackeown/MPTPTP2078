%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IrrlBDah7k

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:18 EST 2020

% Result     : Theorem 15.31s
% Output     : Refutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :  388 (2003 expanded)
%              Number of leaves         :   32 ( 655 expanded)
%              Depth                    :   44
%              Number of atoms          : 3831 (20041 expanded)
%              Number of equality atoms :  186 (1394 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_funct_1 @ X24 )
        = ( k4_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('7',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

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

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34
       != ( k6_relat_1 @ X33 ) )
      | ( ( k1_relat_1 @ X34 )
        = X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('10',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X33 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X33 ) )
        = X33 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('15',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('23',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('30',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','32'])).

thf('34',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('41',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('48',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('77',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','86'])).

thf('88',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('91',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('92',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('94',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('107',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('108',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('112',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','114'])).

thf('116',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('122',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('124',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('126',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('127',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('139',plain,(
    ! [X9: $i] :
      ( ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('140',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('141',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('143',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('144',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('145',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('146',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','155'])).

thf('157',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['142','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('166',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['164','170'])).

thf('172',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['140','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['139','174'])).

thf('176',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['138','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('181',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('182',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('183',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['182','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['181','187'])).

thf('189',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('193',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('194',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('195',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['194','199'])).

thf('201',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X1 ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['193','204'])).

thf('206',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('207',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('209',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['192','210'])).

thf('212',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('213',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('214',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('216',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['211','212','214','215'])).

thf('217',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['216','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('224',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('225',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['191','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['180','226'])).

thf('228',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X8: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('231',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('232',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('233',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['232','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['231','238'])).

thf('240',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['230','242'])).

thf('244',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['211','212','214','215'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('248',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('252',plain,(
    ! [X33: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['245','253'])).

thf('255',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('258',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('259',plain,(
    ! [X9: $i] :
      ( ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('260',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['258','263'])).

thf('265',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('266',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['264','265'])).

thf('267',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['257','268'])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['256','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('273',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('274',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['270','271','272','273'])).

thf('275',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['229','275'])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['179','277'])).

thf('279',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','278'])).

thf('280',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['279','280'])).

thf('282',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','281'])).

thf('283',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['123','284'])).

thf('286',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['122','285'])).

thf('287',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('290',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['121','290'])).

thf('292',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('294',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','293'])).

thf('295',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('297',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X30 @ X31 ) @ X32 )
        = ( k1_funct_1 @ X31 @ ( k1_funct_1 @ X30 @ X32 ) ) )
      | ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ ( k5_relat_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('298',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['296','297'])).

thf('299',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_funct_1 @ X24 )
        = ( k4_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('302',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('303',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( X20
       != ( k2_relat_1 @ X18 ) )
      | ( r2_hidden @ ( sk_D_1 @ X21 @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('304',plain,(
    ! [X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ X18 ) )
      | ( r2_hidden @ ( sk_D_1 @ X21 @ X18 ) @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['303'])).

thf('305',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['302','304'])).

thf('306',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['305','306','307'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('309',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ X36 ) )
      | ( X37
        = ( k1_funct_1 @ ( k2_funct_1 @ X36 ) @ ( k1_funct_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('310',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( X20
       != ( k2_relat_1 @ X18 ) )
      | ( X21
        = ( k1_funct_1 @ X18 @ ( sk_D_1 @ X21 @ X18 ) ) )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('315',plain,(
    ! [X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ X18 ) )
      | ( X21
        = ( k1_funct_1 @ X18 @ ( sk_D_1 @ X21 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['313','315'])).

thf('317',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['316','317','318'])).

thf('320',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['310','311','312','319','320'])).

thf('322',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['301','321'])).

thf('323',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['322','323','324','325'])).

thf('327',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['316','317','318'])).

thf('328',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['298','299','300','326','327'])).

thf('329',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_funct_1 @ X24 )
        = ( k4_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('330',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['330'])).

thf('332',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['329','331'])).

thf('333',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['332','333','334','335'])).

thf('337',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['310','311','312','319','320'])).

thf('338',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['330'])).

thf('339',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['316','317','318'])).

thf('341',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['339','340'])).

thf('342',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['330'])).

thf('344',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['342','343'])).

thf('345',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['336','344'])).

thf('346',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['328','345'])).

thf('347',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','346'])).

thf('348',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,(
    ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['347','348','349','350'])).

thf('352',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','351'])).

thf('353',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,(
    $false ),
    inference(demod,[status(thm)],['352','353'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IrrlBDah7k
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.31/15.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.31/15.53  % Solved by: fo/fo7.sh
% 15.31/15.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.31/15.53  % done 9861 iterations in 15.087s
% 15.31/15.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.31/15.53  % SZS output start Refutation
% 15.31/15.53  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 15.31/15.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 15.31/15.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.31/15.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 15.31/15.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.31/15.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 15.31/15.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.31/15.53  thf(sk_B_type, type, sk_B: $i).
% 15.31/15.53  thf(sk_A_type, type, sk_A: $i).
% 15.31/15.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 15.31/15.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.31/15.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 15.31/15.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.31/15.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.31/15.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 15.31/15.53  thf(dt_k4_relat_1, axiom,
% 15.31/15.53    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 15.31/15.53  thf('0', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf(d9_funct_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.31/15.53       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 15.31/15.53  thf('1', plain,
% 15.31/15.53      (![X24 : $i]:
% 15.31/15.53         (~ (v2_funct_1 @ X24)
% 15.31/15.53          | ((k2_funct_1 @ X24) = (k4_relat_1 @ X24))
% 15.31/15.53          | ~ (v1_funct_1 @ X24)
% 15.31/15.53          | ~ (v1_relat_1 @ X24))),
% 15.31/15.53      inference('cnf', [status(esa)], [d9_funct_1])).
% 15.31/15.53  thf(dt_k2_funct_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.31/15.53       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 15.31/15.53         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 15.31/15.53  thf('2', plain,
% 15.31/15.53      (![X25 : $i]:
% 15.31/15.53         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 15.31/15.53          | ~ (v1_funct_1 @ X25)
% 15.31/15.53          | ~ (v1_relat_1 @ X25))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 15.31/15.53  thf('3', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_funct_1 @ X0)
% 15.31/15.53          | ~ (v2_funct_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_funct_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['1', '2'])).
% 15.31/15.53  thf('4', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v2_funct_1 @ X0)
% 15.31/15.53          | ~ (v1_funct_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['3'])).
% 15.31/15.53  thf(t37_relat_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( v1_relat_1 @ A ) =>
% 15.31/15.53       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 15.31/15.53         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 15.31/15.53  thf('5', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k2_relat_1 @ X9) = (k1_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf(t80_relat_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( v1_relat_1 @ A ) =>
% 15.31/15.53       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 15.31/15.53  thf('6', plain,
% 15.31/15.53      (![X16 : $i]:
% 15.31/15.53         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 15.31/15.53          | ~ (v1_relat_1 @ X16))),
% 15.31/15.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 15.31/15.53  thf('7', plain,
% 15.31/15.53      (![X16 : $i]:
% 15.31/15.53         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 15.31/15.53          | ~ (v1_relat_1 @ X16))),
% 15.31/15.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 15.31/15.53  thf(involutiveness_k4_relat_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 15.31/15.53  thf('8', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf(t34_funct_1, axiom,
% 15.31/15.53    (![A:$i,B:$i]:
% 15.31/15.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.31/15.53       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 15.31/15.53         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 15.31/15.53           ( ![C:$i]:
% 15.31/15.53             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 15.31/15.53  thf('9', plain,
% 15.31/15.53      (![X33 : $i, X34 : $i]:
% 15.31/15.53         (((X34) != (k6_relat_1 @ X33))
% 15.31/15.53          | ((k1_relat_1 @ X34) = (X33))
% 15.31/15.53          | ~ (v1_funct_1 @ X34)
% 15.31/15.53          | ~ (v1_relat_1 @ X34))),
% 15.31/15.53      inference('cnf', [status(esa)], [t34_funct_1])).
% 15.31/15.53  thf('10', plain,
% 15.31/15.53      (![X33 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k6_relat_1 @ X33))
% 15.31/15.53          | ~ (v1_funct_1 @ (k6_relat_1 @ X33))
% 15.31/15.53          | ((k1_relat_1 @ (k6_relat_1 @ X33)) = (X33)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['9'])).
% 15.31/15.53  thf(fc3_funct_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 15.31/15.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 15.31/15.53  thf('11', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('12', plain, (![X27 : $i]: (v1_funct_1 @ (k6_relat_1 @ X27))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('13', plain, (![X33 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 15.31/15.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 15.31/15.53  thf('14', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf('15', plain,
% 15.31/15.53      (![X16 : $i]:
% 15.31/15.53         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 15.31/15.53          | ~ (v1_relat_1 @ X16))),
% 15.31/15.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 15.31/15.53  thf('16', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 15.31/15.53            = (k4_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['14', '15'])).
% 15.31/15.53  thf('17', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('18', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 15.31/15.53              = (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('clc', [status(thm)], ['16', '17'])).
% 15.31/15.53  thf('19', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 15.31/15.53            = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['13', '18'])).
% 15.31/15.53  thf('20', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('21', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 15.31/15.53           = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['19', '20'])).
% 15.31/15.53  thf('22', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('23', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf(t54_relat_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( v1_relat_1 @ A ) =>
% 15.31/15.53       ( ![B:$i]:
% 15.31/15.53         ( ( v1_relat_1 @ B ) =>
% 15.31/15.53           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 15.31/15.53             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 15.31/15.53  thf('24', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('25', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('sup+', [status(thm)], ['23', '24'])).
% 15.31/15.53  thf('26', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0)))),
% 15.31/15.53      inference('sup-', [status(thm)], ['22', '25'])).
% 15.31/15.53  thf('27', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['26'])).
% 15.31/15.53  thf('28', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)) @ 
% 15.31/15.53               (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['21', '27'])).
% 15.31/15.53  thf('29', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 15.31/15.53           = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['19', '20'])).
% 15.31/15.53  thf('30', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('31', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('32', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((k4_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)))
% 15.31/15.53           = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 15.31/15.53  thf('33', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['8', '32'])).
% 15.31/15.53  thf('34', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('35', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('36', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('37', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 15.31/15.53            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['35', '36'])).
% 15.31/15.53  thf('38', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('39', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 15.31/15.53            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('demod', [status(thm)], ['37', '38'])).
% 15.31/15.53  thf('40', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('41', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf('42', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('43', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['41', '42'])).
% 15.31/15.53  thf('44', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53              = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['40', '43'])).
% 15.31/15.53  thf('45', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['44'])).
% 15.31/15.53  thf('46', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 15.31/15.53            = (k5_relat_1 @ X1 @ (k4_relat_1 @ (k6_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['39', '45'])).
% 15.31/15.53  thf('47', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('48', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('49', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 15.31/15.53            = (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('demod', [status(thm)], ['46', '47', '48'])).
% 15.31/15.53  thf('50', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X1)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 15.31/15.53              = (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['49'])).
% 15.31/15.53  thf('51', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53            = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['7', '50'])).
% 15.31/15.53  thf('52', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53              = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['51'])).
% 15.31/15.53  thf('53', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X1)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 15.31/15.53              = (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['49'])).
% 15.31/15.53  thf('54', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 15.31/15.53            = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['52', '53'])).
% 15.31/15.53  thf('55', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 15.31/15.53              = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['54'])).
% 15.31/15.53  thf('56', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X1)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 15.31/15.53              = (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['49'])).
% 15.31/15.53  thf('57', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ 
% 15.31/15.53            (k4_relat_1 @ 
% 15.31/15.53             (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 15.31/15.53            = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['55', '56'])).
% 15.31/15.53  thf('58', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ 
% 15.31/15.53              (k4_relat_1 @ 
% 15.31/15.53               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 15.31/15.53              = (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['57'])).
% 15.31/15.53  thf('59', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ 
% 15.31/15.53            (k4_relat_1 @ 
% 15.31/15.53             (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 15.31/15.53            = (X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['6', '58'])).
% 15.31/15.53  thf('60', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ 
% 15.31/15.53              (k4_relat_1 @ 
% 15.31/15.53               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 15.31/15.53              = (X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['59'])).
% 15.31/15.53  thf('61', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 15.31/15.53              = (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('clc', [status(thm)], ['16', '17'])).
% 15.31/15.53  thf('62', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['26'])).
% 15.31/15.53  thf('63', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))) @ 
% 15.31/15.53               X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 15.31/15.53      inference('sup+', [status(thm)], ['61', '62'])).
% 15.31/15.53  thf('64', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('65', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))) @ 
% 15.31/15.53               X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['63', '64'])).
% 15.31/15.53  thf('66', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53              = (k5_relat_1 @ 
% 15.31/15.53                 (k4_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))) @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['65'])).
% 15.31/15.53  thf('67', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('68', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['66', '67'])).
% 15.31/15.53  thf('69', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('70', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('71', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('sup+', [status(thm)], ['69', '70'])).
% 15.31/15.53  thf('72', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('73', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('demod', [status(thm)], ['71', '72'])).
% 15.31/15.53  thf('74', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['26'])).
% 15.31/15.53  thf('75', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['73', '74'])).
% 15.31/15.53  thf('76', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('77', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('78', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 15.31/15.53            = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['75', '76', '77'])).
% 15.31/15.53  thf('79', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 15.31/15.53              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['78'])).
% 15.31/15.53  thf('80', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 15.31/15.53            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['68', '79'])).
% 15.31/15.53  thf('81', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 15.31/15.53              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['80'])).
% 15.31/15.53  thf('82', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 15.31/15.53              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['78'])).
% 15.31/15.53  thf('83', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ 
% 15.31/15.53            (k4_relat_1 @ 
% 15.31/15.53             (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 15.31/15.53            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['81', '82'])).
% 15.31/15.53  thf('84', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ 
% 15.31/15.53              (k4_relat_1 @ 
% 15.31/15.53               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 15.31/15.53              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['83'])).
% 15.31/15.53  thf('85', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((X0) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['60', '84'])).
% 15.31/15.53  thf('86', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((X0) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['85'])).
% 15.31/15.53  thf('87', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k4_relat_1 @ X0)
% 15.31/15.53            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53               (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['5', '86'])).
% 15.31/15.53  thf('88', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('89', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k4_relat_1 @ X0)
% 15.31/15.53              = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53                 (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('clc', [status(thm)], ['87', '88'])).
% 15.31/15.53  thf('90', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('91', plain,
% 15.31/15.53      (![X16 : $i]:
% 15.31/15.53         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 15.31/15.53          | ~ (v1_relat_1 @ X16))),
% 15.31/15.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 15.31/15.53  thf('92', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf('93', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['44'])).
% 15.31/15.53  thf('94', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('95', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 15.31/15.53      inference('sup+', [status(thm)], ['93', '94'])).
% 15.31/15.53  thf('96', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | (v1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ X1))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['92', '95'])).
% 15.31/15.53  thf('97', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) @ 
% 15.31/15.53              (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['91', '96'])).
% 15.31/15.53  thf('98', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('99', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) @ 
% 15.31/15.53              (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['97', '98'])).
% 15.31/15.53  thf('100', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) @ 
% 15.31/15.53              (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['99'])).
% 15.31/15.53  thf('101', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) @ 
% 15.31/15.53              (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['90', '100'])).
% 15.31/15.53  thf('102', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('103', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) @ 
% 15.31/15.53              (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('demod', [status(thm)], ['101', '102'])).
% 15.31/15.53  thf('104', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('105', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('demod', [status(thm)], ['103', '104'])).
% 15.31/15.53  thf('106', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('107', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf(t45_relat_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( v1_relat_1 @ A ) =>
% 15.31/15.53       ( ![B:$i]:
% 15.31/15.53         ( ( v1_relat_1 @ B ) =>
% 15.31/15.53           ( r1_tarski @
% 15.31/15.53             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 15.31/15.53  thf('108', plain,
% 15.31/15.53      (![X10 : $i, X11 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X10)
% 15.31/15.53          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 15.31/15.53             (k2_relat_1 @ X10))
% 15.31/15.53          | ~ (v1_relat_1 @ X11))),
% 15.31/15.53      inference('cnf', [status(esa)], [t45_relat_1])).
% 15.31/15.53  thf('109', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))) @ 
% 15.31/15.53           (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['107', '108'])).
% 15.31/15.53  thf('110', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r1_tarski @ 
% 15.31/15.53             (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))) @ 
% 15.31/15.53             (k1_relat_1 @ X0)))),
% 15.31/15.53      inference('sup-', [status(thm)], ['106', '109'])).
% 15.31/15.53  thf('111', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))) @ 
% 15.31/15.53           (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['110'])).
% 15.31/15.53  thf(t46_relat_1, axiom,
% 15.31/15.53    (![A:$i]:
% 15.31/15.53     ( ( v1_relat_1 @ A ) =>
% 15.31/15.53       ( ![B:$i]:
% 15.31/15.53         ( ( v1_relat_1 @ B ) =>
% 15.31/15.53           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 15.31/15.53             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 15.31/15.53  thf('112', plain,
% 15.31/15.53      (![X12 : $i, X13 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X12)
% 15.31/15.53          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) = (k1_relat_1 @ X13))
% 15.31/15.53          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 15.31/15.53          | ~ (v1_relat_1 @ X13))),
% 15.31/15.53      inference('cnf', [status(esa)], [t46_relat_1])).
% 15.31/15.53  thf('113', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ((k1_relat_1 @ 
% 15.31/15.53              (k5_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)) @ X0))
% 15.31/15.53              = (k1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup-', [status(thm)], ['111', '112'])).
% 15.31/15.53  thf('114', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k1_relat_1 @ 
% 15.31/15.53            (k5_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)) @ X0))
% 15.31/15.53            = (k1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['113'])).
% 15.31/15.53  thf('115', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 15.31/15.53          | ((k1_relat_1 @ 
% 15.31/15.53              (k5_relat_1 @ 
% 15.31/15.53               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53                (k4_relat_1 @ X0)) @ 
% 15.31/15.53               X0))
% 15.31/15.53              = (k1_relat_1 @ 
% 15.31/15.53                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53                  (k4_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['105', '114'])).
% 15.31/15.53  thf('116', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('117', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k1_relat_1 @ 
% 15.31/15.53              (k5_relat_1 @ 
% 15.31/15.53               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53                (k4_relat_1 @ X0)) @ 
% 15.31/15.53               X0))
% 15.31/15.53              = (k1_relat_1 @ 
% 15.31/15.53                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53                  (k4_relat_1 @ X0)))))),
% 15.31/15.53      inference('demod', [status(thm)], ['115', '116'])).
% 15.31/15.53  thf('118', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k1_relat_1 @ 
% 15.31/15.53            (k5_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0)) @ 
% 15.31/15.53             X0))
% 15.31/15.53            = (k1_relat_1 @ 
% 15.31/15.53               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53                (k4_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['117'])).
% 15.31/15.53  thf('119', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 15.31/15.53            = (k1_relat_1 @ 
% 15.31/15.53               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53                (k4_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['89', '118'])).
% 15.31/15.53  thf('120', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X0))
% 15.31/15.53              = (k1_relat_1 @ 
% 15.31/15.53                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53                  (k4_relat_1 @ X0)))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['119'])).
% 15.31/15.53  thf('121', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('demod', [status(thm)], ['103', '104'])).
% 15.31/15.53  thf('122', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('123', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 15.31/15.53            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('demod', [status(thm)], ['71', '72'])).
% 15.31/15.53  thf('124', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf('125', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 15.31/15.53              = (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('clc', [status(thm)], ['16', '17'])).
% 15.31/15.53  thf('126', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf('127', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('128', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) @ 
% 15.31/15.53              (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('demod', [status(thm)], ['101', '102'])).
% 15.31/15.53  thf('129', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ 
% 15.31/15.53           (k4_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['127', '128'])).
% 15.31/15.53  thf('130', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('131', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ 
% 15.31/15.53           (k4_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['129', '130'])).
% 15.31/15.53  thf('132', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k4_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['131'])).
% 15.31/15.53  thf('133', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ 
% 15.31/15.53           (k4_relat_1 @ 
% 15.31/15.53            (k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['126', '132'])).
% 15.31/15.53  thf('134', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('135', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k4_relat_1 @ 
% 15.31/15.53              (k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 15.31/15.53               (k6_relat_1 @ (k1_relat_1 @ X0))))))),
% 15.31/15.53      inference('clc', [status(thm)], ['133', '134'])).
% 15.31/15.53  thf('136', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['125', '135'])).
% 15.31/15.53  thf('137', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['136'])).
% 15.31/15.53  thf('138', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf('139', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k2_relat_1 @ X9) = (k1_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf('140', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf(t57_funct_1, conjecture,
% 15.31/15.53    (![A:$i,B:$i]:
% 15.31/15.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.31/15.53       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 15.31/15.53         ( ( ( A ) =
% 15.31/15.53             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 15.31/15.53           ( ( A ) =
% 15.31/15.53             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 15.31/15.53  thf(zf_stmt_0, negated_conjecture,
% 15.31/15.53    (~( ![A:$i,B:$i]:
% 15.31/15.53        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.31/15.53          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 15.31/15.53            ( ( ( A ) =
% 15.31/15.53                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 15.31/15.53              ( ( A ) =
% 15.31/15.53                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 15.31/15.53    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 15.31/15.53  thf('141', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 15.31/15.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.53  thf('142', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('143', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf('144', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('145', plain,
% 15.31/15.53      (![X16 : $i]:
% 15.31/15.53         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 15.31/15.53          | ~ (v1_relat_1 @ X16))),
% 15.31/15.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 15.31/15.53  thf('146', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('147', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))) @ 
% 15.31/15.53           (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['110'])).
% 15.31/15.53  thf(d3_tarski, axiom,
% 15.31/15.53    (![A:$i,B:$i]:
% 15.31/15.53     ( ( r1_tarski @ A @ B ) <=>
% 15.31/15.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 15.31/15.53  thf('148', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X0 @ X1)
% 15.31/15.53          | (r2_hidden @ X0 @ X2)
% 15.31/15.53          | ~ (r1_tarski @ X1 @ X2))),
% 15.31/15.53      inference('cnf', [status(esa)], [d3_tarski])).
% 15.31/15.53  thf('149', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (r2_hidden @ X2 @ 
% 15.31/15.53               (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['147', '148'])).
% 15.31/15.53  thf('150', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X2 @ 
% 15.31/15.53             (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('sup-', [status(thm)], ['146', '149'])).
% 15.31/15.53  thf('151', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (r2_hidden @ X2 @ 
% 15.31/15.53               (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['150'])).
% 15.31/15.53  thf('152', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['145', '151'])).
% 15.31/15.53  thf('153', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('154', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 15.31/15.53      inference('demod', [status(thm)], ['152', '153'])).
% 15.31/15.53  thf('155', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['154'])).
% 15.31/15.53  thf('156', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 15.31/15.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 15.31/15.53      inference('sup-', [status(thm)], ['144', '155'])).
% 15.31/15.53  thf('157', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('158', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['156', '157'])).
% 15.31/15.53  thf('159', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup-', [status(thm)], ['143', '158'])).
% 15.31/15.53  thf('160', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 15.31/15.53      inference('sup-', [status(thm)], ['142', '159'])).
% 15.31/15.53  thf('161', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['160'])).
% 15.31/15.53  thf('162', plain,
% 15.31/15.53      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.53        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['141', '161'])).
% 15.31/15.53  thf('163', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.53  thf('164', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 15.31/15.53      inference('demod', [status(thm)], ['162', '163'])).
% 15.31/15.53  thf('165', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('166', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf('167', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['160'])).
% 15.31/15.53  thf('168', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['166', '167'])).
% 15.31/15.53  thf('169', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 15.31/15.53      inference('sup-', [status(thm)], ['165', '168'])).
% 15.31/15.53  thf('170', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 15.31/15.53          | (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['169'])).
% 15.31/15.53  thf('171', plain,
% 15.31/15.53      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 15.31/15.53        | (r2_hidden @ sk_A @ 
% 15.31/15.53           (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['164', '170'])).
% 15.31/15.53  thf('172', plain,
% 15.31/15.53      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.53        | (r2_hidden @ sk_A @ 
% 15.31/15.53           (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['140', '171'])).
% 15.31/15.53  thf('173', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.53  thf('174', plain,
% 15.31/15.53      ((r2_hidden @ sk_A @ 
% 15.31/15.53        (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 15.31/15.53      inference('demod', [status(thm)], ['172', '173'])).
% 15.31/15.53  thf('175', plain,
% 15.31/15.53      (((r2_hidden @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 15.31/15.53        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 15.31/15.53      inference('sup+', [status(thm)], ['139', '174'])).
% 15.31/15.53  thf('176', plain,
% 15.31/15.53      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.53        | ~ (v1_relat_1 @ sk_B)
% 15.31/15.53        | (r2_hidden @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['138', '175'])).
% 15.31/15.53  thf('177', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.53  thf('178', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.53  thf('179', plain,
% 15.31/15.53      ((r2_hidden @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 15.31/15.53      inference('demod', [status(thm)], ['176', '177', '178'])).
% 15.31/15.53  thf('180', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf('181', plain,
% 15.31/15.53      (![X16 : $i]:
% 15.31/15.53         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 15.31/15.53          | ~ (v1_relat_1 @ X16))),
% 15.31/15.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 15.31/15.53  thf('182', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('183', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('184', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 15.31/15.53      inference('sup+', [status(thm)], ['93', '94'])).
% 15.31/15.53  thf('185', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['183', '184'])).
% 15.31/15.53  thf('186', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 15.31/15.53      inference('simplify', [status(thm)], ['185'])).
% 15.31/15.53  thf('187', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['182', '186'])).
% 15.31/15.53  thf('188', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ X0 @ 
% 15.31/15.53              (k4_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup-', [status(thm)], ['181', '187'])).
% 15.31/15.53  thf('189', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('190', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ X0 @ 
% 15.31/15.53              (k4_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['188', '189'])).
% 15.31/15.53  thf('191', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ X0 @ 
% 15.31/15.53              (k4_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['190'])).
% 15.31/15.53  thf('192', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf('193', plain,
% 15.31/15.53      (![X16 : $i]:
% 15.31/15.53         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 15.31/15.53          | ~ (v1_relat_1 @ X16))),
% 15.31/15.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 15.31/15.53  thf('194', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('195', plain, (![X33 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 15.31/15.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 15.31/15.53  thf('196', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))) @ 
% 15.31/15.53           (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['110'])).
% 15.31/15.53  thf('197', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ 
% 15.31/15.53           (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ (k6_relat_1 @ X0)))) @ 
% 15.31/15.53           X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('sup+', [status(thm)], ['195', '196'])).
% 15.31/15.53  thf('198', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('199', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ 
% 15.31/15.53           (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ (k6_relat_1 @ X0)))) @ 
% 15.31/15.53           X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('demod', [status(thm)], ['197', '198'])).
% 15.31/15.53  thf('200', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ 
% 15.31/15.53           (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 15.31/15.53           X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['194', '199'])).
% 15.31/15.53  thf('201', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('202', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ 
% 15.31/15.53           (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 15.31/15.53           X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['200', '201'])).
% 15.31/15.53  thf('203', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('204', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r1_tarski @ 
% 15.31/15.53             (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 15.31/15.53             X1))),
% 15.31/15.53      inference('clc', [status(thm)], ['202', '203'])).
% 15.31/15.53  thf('205', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup+', [status(thm)], ['193', '204'])).
% 15.31/15.53  thf('206', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('207', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('208', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0))) @ X0)),
% 15.31/15.53      inference('demod', [status(thm)], ['205', '206', '207'])).
% 15.31/15.53  thf(d10_xboole_0, axiom,
% 15.31/15.53    (![A:$i,B:$i]:
% 15.31/15.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.31/15.53  thf('209', plain,
% 15.31/15.53      (![X4 : $i, X6 : $i]:
% 15.31/15.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 15.31/15.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.31/15.53  thf('210', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0))))
% 15.31/15.53          | ((X0) = (k2_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['208', '209'])).
% 15.31/15.53  thf('211', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 15.31/15.53          | ((X0) = (k2_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['192', '210'])).
% 15.31/15.53  thf('212', plain, (![X33 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 15.31/15.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 15.31/15.53  thf('213', plain,
% 15.31/15.53      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 15.31/15.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.31/15.53  thf('214', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 15.31/15.53      inference('simplify', [status(thm)], ['213'])).
% 15.31/15.53  thf('215', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('216', plain,
% 15.31/15.53      (![X0 : $i]: ((X0) = (k2_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0))))),
% 15.31/15.53      inference('demod', [status(thm)], ['211', '212', '214', '215'])).
% 15.31/15.53  thf('217', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf('218', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) @ 
% 15.31/15.53              (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('demod', [status(thm)], ['101', '102'])).
% 15.31/15.53  thf('219', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ 
% 15.31/15.53           (k5_relat_1 @ 
% 15.31/15.53            (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))) @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['217', '218'])).
% 15.31/15.53  thf('220', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('221', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (v1_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ 
% 15.31/15.53              (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 15.31/15.53              X0)))),
% 15.31/15.53      inference('clc', [status(thm)], ['219', '220'])).
% 15.31/15.53  thf('222', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ 
% 15.31/15.53           (k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['216', '221'])).
% 15.31/15.53  thf('223', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((k5_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 15.31/15.53           = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['19', '20'])).
% 15.31/15.53  thf('224', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('225', plain,
% 15.31/15.53      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['222', '223', '224'])).
% 15.31/15.53  thf('226', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ 
% 15.31/15.53           (k5_relat_1 @ X0 @ 
% 15.31/15.53            (k4_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['191', '225'])).
% 15.31/15.53  thf('227', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['180', '226'])).
% 15.31/15.53  thf('228', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('229', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['227', '228'])).
% 15.31/15.53  thf('230', plain,
% 15.31/15.53      (![X8 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k4_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 15.31/15.53      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 15.31/15.53  thf('231', plain,
% 15.31/15.53      (![X16 : $i]:
% 15.31/15.53         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 15.31/15.53          | ~ (v1_relat_1 @ X16))),
% 15.31/15.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 15.31/15.53  thf('232', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('233', plain,
% 15.31/15.53      (![X14 : $i, X15 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X14)
% 15.31/15.53          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 15.31/15.53              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 15.31/15.53          | ~ (v1_relat_1 @ X15))),
% 15.31/15.53      inference('cnf', [status(esa)], [t54_relat_1])).
% 15.31/15.53  thf('234', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))) @ 
% 15.31/15.53           (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['110'])).
% 15.31/15.53  thf('235', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 15.31/15.53           (k1_relat_1 @ X1))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['233', '234'])).
% 15.31/15.53  thf('236', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | (r1_tarski @ 
% 15.31/15.53             (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 15.31/15.53             (k1_relat_1 @ X1)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['235'])).
% 15.31/15.53  thf('237', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r1_tarski @ 
% 15.31/15.53             (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 15.31/15.53             (k1_relat_1 @ X1))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup-', [status(thm)], ['232', '236'])).
% 15.31/15.53  thf('238', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X1)
% 15.31/15.53          | (r1_tarski @ 
% 15.31/15.53             (k2_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 15.31/15.53             (k1_relat_1 @ X1))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['237'])).
% 15.31/15.53  thf('239', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['231', '238'])).
% 15.31/15.53  thf('240', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('241', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['239', '240'])).
% 15.31/15.53  thf('242', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['241'])).
% 15.31/15.53  thf('243', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['230', '242'])).
% 15.31/15.53  thf('244', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('245', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('clc', [status(thm)], ['243', '244'])).
% 15.31/15.53  thf('246', plain,
% 15.31/15.53      (![X0 : $i]: ((X0) = (k2_relat_1 @ (k4_relat_1 @ (k6_relat_1 @ X0))))),
% 15.31/15.53      inference('demod', [status(thm)], ['211', '212', '214', '215'])).
% 15.31/15.53  thf('247', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('248', plain, (![X0 : $i]: ((X0) = (k2_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['246', '247'])).
% 15.31/15.53  thf('249', plain,
% 15.31/15.53      (![X12 : $i, X13 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X12)
% 15.31/15.53          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) = (k1_relat_1 @ X13))
% 15.31/15.53          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 15.31/15.53          | ~ (v1_relat_1 @ X13))),
% 15.31/15.53      inference('cnf', [status(esa)], [t46_relat_1])).
% 15.31/15.53  thf('250', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 15.31/15.53          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 15.31/15.53              = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('sup-', [status(thm)], ['248', '249'])).
% 15.31/15.53  thf('251', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('252', plain, (![X33 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 15.31/15.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 15.31/15.53  thf('253', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 15.31/15.53          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X1))),
% 15.31/15.53      inference('demod', [status(thm)], ['250', '251', '252'])).
% 15.31/15.53  thf('254', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | ((k1_relat_1 @ 
% 15.31/15.53              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 15.31/15.53               (k4_relat_1 @ X0)))
% 15.31/15.53              = (k2_relat_1 @ X0)))),
% 15.31/15.53      inference('sup-', [status(thm)], ['245', '253'])).
% 15.31/15.53  thf('255', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('256', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (((k1_relat_1 @ 
% 15.31/15.53            (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0)))
% 15.31/15.53            = (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('clc', [status(thm)], ['254', '255'])).
% 15.31/15.53  thf('257', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 15.31/15.53            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['44'])).
% 15.31/15.53  thf('258', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k1_relat_1 @ X9) = (k2_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf('259', plain,
% 15.31/15.53      (![X9 : $i]:
% 15.31/15.53         (((k2_relat_1 @ X9) = (k1_relat_1 @ (k4_relat_1 @ X9)))
% 15.31/15.53          | ~ (v1_relat_1 @ X9))),
% 15.31/15.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 15.31/15.53  thf('260', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['241'])).
% 15.31/15.53  thf('261', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 15.31/15.53           (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['259', '260'])).
% 15.31/15.53  thf('262', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('263', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 15.31/15.53             (k2_relat_1 @ X0)))),
% 15.31/15.53      inference('clc', [status(thm)], ['261', '262'])).
% 15.31/15.53  thf('264', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('sup+', [status(thm)], ['258', '263'])).
% 15.31/15.53  thf('265', plain,
% 15.31/15.53      (![X7 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X7)) | ~ (v1_relat_1 @ X7))),
% 15.31/15.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 15.31/15.53  thf('266', plain,
% 15.31/15.53      (![X0 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 15.31/15.53      inference('clc', [status(thm)], ['264', '265'])).
% 15.31/15.53  thf('267', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X0 @ X1)
% 15.31/15.53          | (r2_hidden @ X0 @ X2)
% 15.31/15.53          | ~ (r1_tarski @ X1 @ X2))),
% 15.31/15.53      inference('cnf', [status(esa)], [d3_tarski])).
% 15.31/15.53  thf('268', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['266', '267'])).
% 15.31/15.53  thf('269', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X2 @ 
% 15.31/15.53             (k1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X1)
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X2 @ 
% 15.31/15.53             (k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))
% 15.31/15.53          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['257', '268'])).
% 15.31/15.53  thf('270', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ 
% 15.31/15.53               (k5_relat_1 @ X0 @ 
% 15.31/15.53                (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 15.31/15.53          | (r2_hidden @ X1 @ 
% 15.31/15.53             (k2_relat_1 @ 
% 15.31/15.53              (k5_relat_1 @ X0 @ 
% 15.31/15.53               (k4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['256', '269'])).
% 15.31/15.53  thf('271', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('272', plain,
% 15.31/15.53      (![X0 : $i]: ((k6_relat_1 @ X0) = (k4_relat_1 @ (k6_relat_1 @ X0)))),
% 15.31/15.53      inference('demod', [status(thm)], ['33', '34'])).
% 15.31/15.53  thf('273', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 15.31/15.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 15.31/15.53  thf('274', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (v1_relat_1 @ 
% 15.31/15.53               (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | (r2_hidden @ X1 @ 
% 15.31/15.53             (k2_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('demod', [status(thm)], ['270', '271', '272', '273'])).
% 15.31/15.53  thf('275', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r2_hidden @ X1 @ 
% 15.31/15.53           (k2_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 15.31/15.53          | ~ (v1_relat_1 @ 
% 15.31/15.53               (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 15.31/15.53      inference('simplify', [status(thm)], ['274'])).
% 15.31/15.53  thf('276', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         (~ (v1_relat_1 @ X0)
% 15.31/15.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0)
% 15.31/15.53          | (r2_hidden @ X1 @ 
% 15.31/15.53             (k2_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['229', '275'])).
% 15.31/15.53  thf('277', plain,
% 15.31/15.53      (![X0 : $i, X1 : $i]:
% 15.31/15.53         ((r2_hidden @ X1 @ 
% 15.31/15.53           (k2_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 15.31/15.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 15.31/15.53          | ~ (v1_relat_1 @ X0))),
% 15.31/15.53      inference('simplify', [status(thm)], ['276'])).
% 15.31/15.53  thf('278', plain,
% 15.31/15.53      ((~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 15.31/15.53        | (r2_hidden @ sk_A @ 
% 15.31/15.53           (k2_relat_1 @ 
% 15.31/15.53            (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 15.31/15.53             (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['179', '277'])).
% 15.31/15.53  thf('279', plain,
% 15.31/15.53      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.53        | (r2_hidden @ sk_A @ 
% 15.31/15.53           (k2_relat_1 @ 
% 15.31/15.53            (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 15.31/15.53             (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['137', '278'])).
% 15.31/15.53  thf('280', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.53  thf('281', plain,
% 15.31/15.53      ((r2_hidden @ sk_A @ 
% 15.31/15.53        (k2_relat_1 @ 
% 15.31/15.53         (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 15.31/15.53          (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))))),
% 15.31/15.53      inference('demod', [status(thm)], ['279', '280'])).
% 15.31/15.53  thf('282', plain,
% 15.31/15.53      (((r2_hidden @ sk_A @ 
% 15.31/15.53         (k2_relat_1 @ 
% 15.31/15.53          (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 15.31/15.53           (k6_relat_1 @ (k2_relat_1 @ sk_B)))))
% 15.31/15.53        | ~ (v1_relat_1 @ sk_B))),
% 15.31/15.53      inference('sup+', [status(thm)], ['124', '281'])).
% 15.31/15.53  thf('283', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.53  thf('284', plain,
% 15.31/15.53      ((r2_hidden @ sk_A @ 
% 15.31/15.53        (k2_relat_1 @ 
% 15.31/15.53         (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 15.31/15.53          (k6_relat_1 @ (k2_relat_1 @ sk_B)))))),
% 15.31/15.53      inference('demod', [status(thm)], ['282', '283'])).
% 15.31/15.53  thf('285', plain,
% 15.31/15.53      (((r2_hidden @ sk_A @ 
% 15.31/15.53         (k2_relat_1 @ 
% 15.31/15.53          (k4_relat_1 @ 
% 15.31/15.53           (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 15.31/15.53            (k4_relat_1 @ sk_B)))))
% 15.31/15.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 15.31/15.53      inference('sup+', [status(thm)], ['123', '284'])).
% 15.31/15.53  thf('286', plain,
% 15.31/15.53      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.53        | (r2_hidden @ sk_A @ 
% 15.31/15.53           (k2_relat_1 @ 
% 15.31/15.53            (k4_relat_1 @ 
% 15.31/15.53             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 15.31/15.53              (k4_relat_1 @ sk_B))))))),
% 15.31/15.53      inference('sup-', [status(thm)], ['122', '285'])).
% 15.31/15.54  thf('287', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('288', plain,
% 15.31/15.54      ((r2_hidden @ sk_A @ 
% 15.31/15.54        (k2_relat_1 @ 
% 15.31/15.54         (k4_relat_1 @ 
% 15.31/15.54          (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 15.31/15.54           (k4_relat_1 @ sk_B)))))),
% 15.31/15.54      inference('demod', [status(thm)], ['286', '287'])).
% 15.31/15.54  thf('289', plain,
% 15.31/15.54      (![X0 : $i, X1 : $i]:
% 15.31/15.54         (~ (r2_hidden @ X1 @ (k2_relat_1 @ (k4_relat_1 @ X0)))
% 15.31/15.54          | ~ (v1_relat_1 @ X0)
% 15.31/15.54          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 15.31/15.54      inference('demod', [status(thm)], ['156', '157'])).
% 15.31/15.54  thf('290', plain,
% 15.31/15.54      (((r2_hidden @ sk_A @ 
% 15.31/15.54         (k1_relat_1 @ 
% 15.31/15.54          (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 15.31/15.54           (k4_relat_1 @ sk_B))))
% 15.31/15.54        | ~ (v1_relat_1 @ 
% 15.31/15.54             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 15.31/15.54              (k4_relat_1 @ sk_B))))),
% 15.31/15.54      inference('sup-', [status(thm)], ['288', '289'])).
% 15.31/15.54  thf('291', plain,
% 15.31/15.54      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.54        | (r2_hidden @ sk_A @ 
% 15.31/15.54           (k1_relat_1 @ 
% 15.31/15.54            (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 15.31/15.54             (k4_relat_1 @ sk_B)))))),
% 15.31/15.54      inference('sup-', [status(thm)], ['121', '290'])).
% 15.31/15.54  thf('292', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('293', plain,
% 15.31/15.54      ((r2_hidden @ sk_A @ 
% 15.31/15.54        (k1_relat_1 @ 
% 15.31/15.54         (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ (k4_relat_1 @ sk_B))))),
% 15.31/15.54      inference('demod', [status(thm)], ['291', '292'])).
% 15.31/15.54  thf('294', plain,
% 15.31/15.54      (((r2_hidden @ sk_A @ 
% 15.31/15.54         (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)))
% 15.31/15.54        | ~ (v1_relat_1 @ sk_B))),
% 15.31/15.54      inference('sup+', [status(thm)], ['120', '293'])).
% 15.31/15.54  thf('295', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('296', plain,
% 15.31/15.54      ((r2_hidden @ sk_A @ 
% 15.31/15.54        (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)))),
% 15.31/15.54      inference('demod', [status(thm)], ['294', '295'])).
% 15.31/15.54  thf(t22_funct_1, axiom,
% 15.31/15.54    (![A:$i,B:$i]:
% 15.31/15.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.31/15.54       ( ![C:$i]:
% 15.31/15.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 15.31/15.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 15.31/15.54             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 15.31/15.54               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 15.31/15.54  thf('297', plain,
% 15.31/15.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 15.31/15.54         (~ (v1_relat_1 @ X30)
% 15.31/15.54          | ~ (v1_funct_1 @ X30)
% 15.31/15.54          | ((k1_funct_1 @ (k5_relat_1 @ X30 @ X31) @ X32)
% 15.31/15.54              = (k1_funct_1 @ X31 @ (k1_funct_1 @ X30 @ X32)))
% 15.31/15.54          | ~ (r2_hidden @ X32 @ (k1_relat_1 @ (k5_relat_1 @ X30 @ X31)))
% 15.31/15.54          | ~ (v1_funct_1 @ X31)
% 15.31/15.54          | ~ (v1_relat_1 @ X31))),
% 15.31/15.54      inference('cnf', [status(esa)], [t22_funct_1])).
% 15.31/15.54  thf('298', plain,
% 15.31/15.54      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.54        | ~ (v1_funct_1 @ sk_B)
% 15.31/15.54        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 15.31/15.54            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 15.31/15.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 15.31/15.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 15.31/15.54      inference('sup-', [status(thm)], ['296', '297'])).
% 15.31/15.54  thf('299', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('300', plain, ((v1_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('301', plain,
% 15.31/15.54      (![X24 : $i]:
% 15.31/15.54         (~ (v2_funct_1 @ X24)
% 15.31/15.54          | ((k2_funct_1 @ X24) = (k4_relat_1 @ X24))
% 15.31/15.54          | ~ (v1_funct_1 @ X24)
% 15.31/15.54          | ~ (v1_relat_1 @ X24))),
% 15.31/15.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 15.31/15.54  thf('302', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf(d5_funct_1, axiom,
% 15.31/15.54    (![A:$i]:
% 15.31/15.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.31/15.54       ( ![B:$i]:
% 15.31/15.54         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 15.31/15.54           ( ![C:$i]:
% 15.31/15.54             ( ( r2_hidden @ C @ B ) <=>
% 15.31/15.54               ( ?[D:$i]:
% 15.31/15.54                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 15.31/15.54                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 15.31/15.54  thf('303', plain,
% 15.31/15.54      (![X18 : $i, X20 : $i, X21 : $i]:
% 15.31/15.54         (((X20) != (k2_relat_1 @ X18))
% 15.31/15.54          | (r2_hidden @ (sk_D_1 @ X21 @ X18) @ (k1_relat_1 @ X18))
% 15.31/15.54          | ~ (r2_hidden @ X21 @ X20)
% 15.31/15.54          | ~ (v1_funct_1 @ X18)
% 15.31/15.54          | ~ (v1_relat_1 @ X18))),
% 15.31/15.54      inference('cnf', [status(esa)], [d5_funct_1])).
% 15.31/15.54  thf('304', plain,
% 15.31/15.54      (![X18 : $i, X21 : $i]:
% 15.31/15.54         (~ (v1_relat_1 @ X18)
% 15.31/15.54          | ~ (v1_funct_1 @ X18)
% 15.31/15.54          | ~ (r2_hidden @ X21 @ (k2_relat_1 @ X18))
% 15.31/15.54          | (r2_hidden @ (sk_D_1 @ X21 @ X18) @ (k1_relat_1 @ X18)))),
% 15.31/15.54      inference('simplify', [status(thm)], ['303'])).
% 15.31/15.54  thf('305', plain,
% 15.31/15.54      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 15.31/15.54        | ~ (v1_funct_1 @ sk_B)
% 15.31/15.54        | ~ (v1_relat_1 @ sk_B))),
% 15.31/15.54      inference('sup-', [status(thm)], ['302', '304'])).
% 15.31/15.54  thf('306', plain, ((v1_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('307', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('308', plain,
% 15.31/15.54      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 15.31/15.54      inference('demod', [status(thm)], ['305', '306', '307'])).
% 15.31/15.54  thf(t56_funct_1, axiom,
% 15.31/15.54    (![A:$i,B:$i]:
% 15.31/15.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.31/15.54       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 15.31/15.54         ( ( ( A ) =
% 15.31/15.54             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 15.31/15.54           ( ( A ) =
% 15.31/15.54             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 15.31/15.54  thf('309', plain,
% 15.31/15.54      (![X36 : $i, X37 : $i]:
% 15.31/15.54         (~ (v2_funct_1 @ X36)
% 15.31/15.54          | ~ (r2_hidden @ X37 @ (k1_relat_1 @ X36))
% 15.31/15.54          | ((X37)
% 15.31/15.54              = (k1_funct_1 @ (k2_funct_1 @ X36) @ (k1_funct_1 @ X36 @ X37)))
% 15.31/15.54          | ~ (v1_funct_1 @ X36)
% 15.31/15.54          | ~ (v1_relat_1 @ X36))),
% 15.31/15.54      inference('cnf', [status(esa)], [t56_funct_1])).
% 15.31/15.54  thf('310', plain,
% 15.31/15.54      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.54        | ~ (v1_funct_1 @ sk_B)
% 15.31/15.54        | ((sk_D_1 @ sk_A @ sk_B)
% 15.31/15.54            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 15.31/15.54               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 15.31/15.54        | ~ (v2_funct_1 @ sk_B))),
% 15.31/15.54      inference('sup-', [status(thm)], ['308', '309'])).
% 15.31/15.54  thf('311', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('312', plain, ((v1_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('313', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('314', plain,
% 15.31/15.54      (![X18 : $i, X20 : $i, X21 : $i]:
% 15.31/15.54         (((X20) != (k2_relat_1 @ X18))
% 15.31/15.54          | ((X21) = (k1_funct_1 @ X18 @ (sk_D_1 @ X21 @ X18)))
% 15.31/15.54          | ~ (r2_hidden @ X21 @ X20)
% 15.31/15.54          | ~ (v1_funct_1 @ X18)
% 15.31/15.54          | ~ (v1_relat_1 @ X18))),
% 15.31/15.54      inference('cnf', [status(esa)], [d5_funct_1])).
% 15.31/15.54  thf('315', plain,
% 15.31/15.54      (![X18 : $i, X21 : $i]:
% 15.31/15.54         (~ (v1_relat_1 @ X18)
% 15.31/15.54          | ~ (v1_funct_1 @ X18)
% 15.31/15.54          | ~ (r2_hidden @ X21 @ (k2_relat_1 @ X18))
% 15.31/15.54          | ((X21) = (k1_funct_1 @ X18 @ (sk_D_1 @ X21 @ X18))))),
% 15.31/15.54      inference('simplify', [status(thm)], ['314'])).
% 15.31/15.54  thf('316', plain,
% 15.31/15.54      ((((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))
% 15.31/15.54        | ~ (v1_funct_1 @ sk_B)
% 15.31/15.54        | ~ (v1_relat_1 @ sk_B))),
% 15.31/15.54      inference('sup-', [status(thm)], ['313', '315'])).
% 15.31/15.54  thf('317', plain, ((v1_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('318', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('319', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 15.31/15.54      inference('demod', [status(thm)], ['316', '317', '318'])).
% 15.31/15.54  thf('320', plain, ((v2_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('321', plain,
% 15.31/15.54      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 15.31/15.54      inference('demod', [status(thm)], ['310', '311', '312', '319', '320'])).
% 15.31/15.54  thf('322', plain,
% 15.31/15.54      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 15.31/15.54        | ~ (v1_relat_1 @ sk_B)
% 15.31/15.54        | ~ (v1_funct_1 @ sk_B)
% 15.31/15.54        | ~ (v2_funct_1 @ sk_B))),
% 15.31/15.54      inference('sup+', [status(thm)], ['301', '321'])).
% 15.31/15.54  thf('323', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('324', plain, ((v1_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('325', plain, ((v2_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('326', plain,
% 15.31/15.54      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 15.31/15.54      inference('demod', [status(thm)], ['322', '323', '324', '325'])).
% 15.31/15.54  thf('327', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 15.31/15.54      inference('demod', [status(thm)], ['316', '317', '318'])).
% 15.31/15.54  thf('328', plain,
% 15.31/15.54      ((((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 15.31/15.54          = (sk_A))
% 15.31/15.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 15.31/15.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 15.31/15.54      inference('demod', [status(thm)], ['298', '299', '300', '326', '327'])).
% 15.31/15.54  thf('329', plain,
% 15.31/15.54      (![X24 : $i]:
% 15.31/15.54         (~ (v2_funct_1 @ X24)
% 15.31/15.54          | ((k2_funct_1 @ X24) = (k4_relat_1 @ X24))
% 15.31/15.54          | ~ (v1_funct_1 @ X24)
% 15.31/15.54          | ~ (v1_relat_1 @ X24))),
% 15.31/15.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 15.31/15.54  thf('330', plain,
% 15.31/15.54      ((((sk_A)
% 15.31/15.54          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 15.31/15.54        | ((sk_A)
% 15.31/15.54            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('331', plain,
% 15.31/15.54      ((((sk_A)
% 15.31/15.54          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 15.31/15.54         <= (~
% 15.31/15.54             (((sk_A)
% 15.31/15.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 15.31/15.54                   sk_A))))),
% 15.31/15.54      inference('split', [status(esa)], ['330'])).
% 15.31/15.54  thf('332', plain,
% 15.31/15.54      (((((sk_A)
% 15.31/15.54           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 15.31/15.54         | ~ (v1_relat_1 @ sk_B)
% 15.31/15.54         | ~ (v1_funct_1 @ sk_B)
% 15.31/15.54         | ~ (v2_funct_1 @ sk_B)))
% 15.31/15.54         <= (~
% 15.31/15.54             (((sk_A)
% 15.31/15.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 15.31/15.54                   sk_A))))),
% 15.31/15.54      inference('sup-', [status(thm)], ['329', '331'])).
% 15.31/15.54  thf('333', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('334', plain, ((v1_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('335', plain, ((v2_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('336', plain,
% 15.31/15.54      ((((sk_A)
% 15.31/15.54          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 15.31/15.54         <= (~
% 15.31/15.54             (((sk_A)
% 15.31/15.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 15.31/15.54                   sk_A))))),
% 15.31/15.54      inference('demod', [status(thm)], ['332', '333', '334', '335'])).
% 15.31/15.54  thf('337', plain,
% 15.31/15.54      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 15.31/15.54      inference('demod', [status(thm)], ['310', '311', '312', '319', '320'])).
% 15.31/15.54  thf('338', plain,
% 15.31/15.54      ((((sk_A)
% 15.31/15.54          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 15.31/15.54         <= (~
% 15.31/15.54             (((sk_A)
% 15.31/15.54                = (k1_funct_1 @ sk_B @ 
% 15.31/15.54                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 15.31/15.54      inference('split', [status(esa)], ['330'])).
% 15.31/15.54  thf('339', plain,
% 15.31/15.54      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 15.31/15.54         <= (~
% 15.31/15.54             (((sk_A)
% 15.31/15.54                = (k1_funct_1 @ sk_B @ 
% 15.31/15.54                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 15.31/15.54      inference('sup-', [status(thm)], ['337', '338'])).
% 15.31/15.54  thf('340', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 15.31/15.54      inference('demod', [status(thm)], ['316', '317', '318'])).
% 15.31/15.54  thf('341', plain,
% 15.31/15.54      ((((sk_A) != (sk_A)))
% 15.31/15.54         <= (~
% 15.31/15.54             (((sk_A)
% 15.31/15.54                = (k1_funct_1 @ sk_B @ 
% 15.31/15.54                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 15.31/15.54      inference('demod', [status(thm)], ['339', '340'])).
% 15.31/15.54  thf('342', plain,
% 15.31/15.54      ((((sk_A)
% 15.31/15.54          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 15.31/15.54      inference('simplify', [status(thm)], ['341'])).
% 15.31/15.54  thf('343', plain,
% 15.31/15.54      (~
% 15.31/15.54       (((sk_A)
% 15.31/15.54          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 15.31/15.54       ~
% 15.31/15.54       (((sk_A)
% 15.31/15.54          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 15.31/15.54      inference('split', [status(esa)], ['330'])).
% 15.31/15.54  thf('344', plain,
% 15.31/15.54      (~
% 15.31/15.54       (((sk_A)
% 15.31/15.54          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 15.31/15.54      inference('sat_resolution*', [status(thm)], ['342', '343'])).
% 15.31/15.54  thf('345', plain,
% 15.31/15.54      (((sk_A)
% 15.31/15.54         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 15.31/15.54      inference('simpl_trail', [status(thm)], ['336', '344'])).
% 15.31/15.54  thf('346', plain,
% 15.31/15.54      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 15.31/15.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 15.31/15.54      inference('simplify_reflect-', [status(thm)], ['328', '345'])).
% 15.31/15.54  thf('347', plain,
% 15.31/15.54      ((~ (v1_relat_1 @ sk_B)
% 15.31/15.54        | ~ (v1_funct_1 @ sk_B)
% 15.31/15.54        | ~ (v2_funct_1 @ sk_B)
% 15.31/15.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 15.31/15.54      inference('sup-', [status(thm)], ['4', '346'])).
% 15.31/15.54  thf('348', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('349', plain, ((v1_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('350', plain, ((v2_funct_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('351', plain, (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 15.31/15.54      inference('demod', [status(thm)], ['347', '348', '349', '350'])).
% 15.31/15.54  thf('352', plain, (~ (v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('sup-', [status(thm)], ['0', '351'])).
% 15.31/15.54  thf('353', plain, ((v1_relat_1 @ sk_B)),
% 15.31/15.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.31/15.54  thf('354', plain, ($false), inference('demod', [status(thm)], ['352', '353'])).
% 15.31/15.54  
% 15.31/15.54  % SZS output end Refutation
% 15.31/15.54  
% 15.31/15.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
