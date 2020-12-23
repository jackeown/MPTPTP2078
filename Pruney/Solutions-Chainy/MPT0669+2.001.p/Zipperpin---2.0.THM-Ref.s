%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xH6KzBsI01

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 255 expanded)
%              Number of leaves         :   14 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          : 1133 (3636 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t86_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
        <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( X24
       != ( k1_funct_1 @ X23 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( k1_funct_1 @ X23 @ X22 ) ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X5 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
        = ( k1_funct_1 @ sk_C @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['44'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('50',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['5'])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( k1_funct_1 @ X23 @ X22 ) ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('53',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('59',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k8_relat_1 @ X0 @ sk_C ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k8_relat_1 @ X0 @ sk_C ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','65'])).

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('68',plain,
    ( ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('78',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['5'])).

thf('80',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('82',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['44'])).

thf('87',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','78','79','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xH6KzBsI01
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 116 iterations in 0.075s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(t86_funct_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.20/0.53         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.53           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.53          ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.20/0.53            ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.53              ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t86_funct_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)
% 0.20/0.53        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))) | 
% 0.20/0.53       ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(fc9_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53       ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) & 
% 0.20/0.53         ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7))
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7))
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((v1_funct_1 @ (k8_relat_1 @ X6 @ X7))
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.20/0.53        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf(t8_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.53         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.53           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.20/0.53          | ((X24) != (k1_funct_1 @ X23 @ X22))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | ~ (v1_relat_1 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X23)
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X22 @ (k1_funct_1 @ X23 @ X22)) @ X23)
% 0.20/0.53          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((((r2_hidden @ 
% 0.20/0.53          (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53          (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | ~ (v1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | (r2_hidden @ 
% 0.20/0.53            (k4_tarski @ sk_A @ 
% 0.20/0.53             (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53            (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.53  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | (r2_hidden @ 
% 0.20/0.53            (k4_tarski @ sk_A @ 
% 0.20/0.53             (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53            (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | (r2_hidden @ 
% 0.20/0.53            (k4_tarski @ sk_A @ 
% 0.20/0.53             (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53            (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '13'])).
% 0.20/0.53  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (((r2_hidden @ 
% 0.20/0.53         (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53         (k8_relat_1 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.53  thf(d12_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( v1_relat_1 @ C ) =>
% 0.20/0.53           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 0.20/0.53             ( ![D:$i,E:$i]:
% 0.20/0.53               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.20/0.53                 ( ( r2_hidden @ E @ A ) & 
% 0.20/0.53                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.20/0.53          | (r2_hidden @ X5 @ X1)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X2)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.20/0.53          | (r2_hidden @ X5 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | (r2_hidden @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A) @ sk_B)
% 0.20/0.53         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.53  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | (r2_hidden @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A) @ sk_B)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | (r2_hidden @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A) @ sk_B)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '22'])).
% 0.20/0.53  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((r2_hidden @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A) @ sk_B))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7))
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((r2_hidden @ 
% 0.20/0.53         (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53         (k8_relat_1 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X2)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.20/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | (r2_hidden @ 
% 0.20/0.53            (k4_tarski @ sk_A @ 
% 0.20/0.53             (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53            sk_C)
% 0.20/0.53         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '30'])).
% 0.20/0.53  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | (r2_hidden @ 
% 0.20/0.53            (k4_tarski @ sk_A @ 
% 0.20/0.53             (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53            sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | (r2_hidden @ 
% 0.20/0.53            (k4_tarski @ sk_A @ 
% 0.20/0.53             (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53            sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '33'])).
% 0.20/0.53  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((r2_hidden @ 
% 0.20/0.53         (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53         sk_C))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.20/0.53          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | ~ (v1_relat_1 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | ((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.20/0.53             = (k1_funct_1 @ sk_C @ sk_A))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.20/0.53          = (k1_funct_1 @ sk_C @ sk_A)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)
% 0.20/0.53        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.20/0.53        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))
% 0.20/0.53         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))) | 
% 0.20/0.53       ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))) | 
% 0.20/0.53       ~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((v1_funct_1 @ (k8_relat_1 @ X6 @ X7))
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7))
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))
% 0.20/0.53         <= (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X23)
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X22 @ (k1_funct_1 @ X23 @ X22)) @ X23)
% 0.20/0.53          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.53      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7))
% 0.20/0.53          | ~ (v1_funct_1 @ X7)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.20/0.53          | ~ (r2_hidden @ X4 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X2)
% 0.20/0.53          | ~ (r2_hidden @ X4 @ X1)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k8_relat_1 @ X1 @ X2))
% 0.20/0.53          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X2 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['57', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ X1)
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X0)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (v1_relat_1 @ sk_C)
% 0.20/0.53           | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53           | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.53              (k8_relat_1 @ X0 @ sk_C))
% 0.20/0.53           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['56', '61'])).
% 0.20/0.53  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.53            (k8_relat_1 @ X0 @ sk_C))
% 0.20/0.53           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.53      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.20/0.53         (k8_relat_1 @ sk_B @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.53             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.20/0.53          | (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | ~ (v1_relat_1 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | ~ (v1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.53         | (r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.53             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | (r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))
% 0.20/0.53         | ~ (v1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.53             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '68'])).
% 0.20/0.53  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))
% 0.20/0.53         | ~ (v1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.53             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | (r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.53             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '72'])).
% 0.20/0.53  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.20/0.53             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.20/0.53       ~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))) | 
% 0.20/0.53       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (((r2_hidden @ 
% 0.20/0.53         (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.53         sk_C))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.20/0.53          | (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | ~ (v1_relat_1 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53         | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.53  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.20/0.53      inference('split', [status(esa)], ['44'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))) | 
% 0.20/0.53       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.53  thf('88', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)],
% 0.20/0.53                ['1', '46', '47', '78', '79', '87'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
