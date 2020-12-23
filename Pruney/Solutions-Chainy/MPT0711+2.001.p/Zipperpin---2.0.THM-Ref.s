%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U6XVi1cbQp

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:11 EST 2020

% Result     : Theorem 11.95s
% Output     : Refutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :  171 (2124 expanded)
%              Number of leaves         :   24 ( 633 expanded)
%              Depth                    :   35
%              Number of atoms          : 1736 (35165 expanded)
%              Number of equality atoms :  118 (3310 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X12 @ X13 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B_1 @ X0 )
        = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) ) )
      | ( r2_hidden @ X14 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

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

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( r2_hidden @ ( sk_D @ X22 @ X21 @ X23 ) @ X22 )
      | ( ( k7_relat_1 @ X23 @ X22 )
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X12 @ X13 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

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
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) @ sk_A @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','29','30','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X12 @ X13 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X12 @ X13 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      = ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('65',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k7_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) )
        = ( k7_relat_1 @ X11 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ ( k1_relat_1 @ X11 ) ) ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k7_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) )
        = ( k7_relat_1 @ X11 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ ( k1_relat_1 @ X11 ) ) ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('72',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X12 @ X13 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( sk_B @ X0 ) ) )
        = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','84'])).

thf('86',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('87',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['64','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','62','63','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','92'])).

thf('94',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('95',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('96',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X12 @ X13 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ ( sk_B @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('103',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B @ X1 ) @ X0 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ ( sk_B @ X1 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( sk_B @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['94','104'])).

thf('106',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('107',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('110',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_B_1 @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','108','109','110','111'])).

thf('113',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('114',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('115',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) ) )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','117'])).

thf('119',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_B_1 @ X0 )
        = ( k7_relat_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','120'])).

thf('122',plain,(
    ! [X25: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X25 )
        = ( k1_funct_1 @ sk_B_1 @ X25 ) )
      | ~ ( r2_hidden @ X25 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_C_1 )
      = ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('126',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_C_1 )
      = ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_B_1 @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k1_funct_1 @ X23 @ ( sk_D @ X22 @ X21 @ X23 ) )
       != ( k1_funct_1 @ X21 @ ( sk_D @ X22 @ X21 @ X23 ) ) )
      | ( ( k7_relat_1 @ X23 @ X22 )
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t165_funct_1])).

thf('130',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B_1 @ X0 )
      = ( k7_relat_1 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ X0 )
      = ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['64','88'])).

thf('140',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) )
     != ( k1_funct_1 @ sk_A @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A @ sk_B_1 ) ) )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_C_1 )
      = ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','136','137','138','139','140','141'])).

thf('143',plain,
    ( ( k7_relat_1 @ sk_B_1 @ sk_C_1 )
    = ( k7_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U6XVi1cbQp
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.95/12.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.95/12.12  % Solved by: fo/fo7.sh
% 11.95/12.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.95/12.12  % done 9586 iterations in 11.662s
% 11.95/12.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.95/12.12  % SZS output start Refutation
% 11.95/12.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.95/12.12  thf(sk_C_1_type, type, sk_C_1: $i).
% 11.95/12.12  thf(sk_B_type, type, sk_B: $i > $i).
% 11.95/12.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.95/12.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.95/12.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.95/12.12  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 11.95/12.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 11.95/12.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.95/12.12  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 11.95/12.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.95/12.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.95/12.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.95/12.12  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 11.95/12.12  thf(sk_A_type, type, sk_A: $i).
% 11.95/12.12  thf(t166_funct_1, conjecture,
% 11.95/12.12    (![A:$i]:
% 11.95/12.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 11.95/12.12       ( ![B:$i]:
% 11.95/12.12         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 11.95/12.12           ( ![C:$i]:
% 11.95/12.12             ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 11.95/12.12                 ( ![D:$i]:
% 11.95/12.12                   ( ( r2_hidden @ D @ C ) =>
% 11.95/12.12                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 11.95/12.12               ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ))).
% 11.95/12.12  thf(zf_stmt_0, negated_conjecture,
% 11.95/12.12    (~( ![A:$i]:
% 11.95/12.12        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 11.95/12.12          ( ![B:$i]:
% 11.95/12.12            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 11.95/12.12              ( ![C:$i]:
% 11.95/12.12                ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 11.95/12.12                    ( ![D:$i]:
% 11.95/12.12                      ( ( r2_hidden @ D @ C ) =>
% 11.95/12.12                        ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) =>
% 11.95/12.12                  ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ) )),
% 11.95/12.12    inference('cnf.neg', [status(esa)], [t166_funct_1])).
% 11.95/12.12  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('1', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf(t192_relat_1, axiom,
% 11.95/12.12    (![A:$i,B:$i]:
% 11.95/12.12     ( ( v1_relat_1 @ B ) =>
% 11.95/12.12       ( ( k7_relat_1 @ B @ A ) =
% 11.95/12.12         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 11.95/12.12  thf('2', plain,
% 11.95/12.12      (![X12 : $i, X13 : $i]:
% 11.95/12.12         (((k7_relat_1 @ X12 @ X13)
% 11.95/12.12            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13)))
% 11.95/12.12          | ~ (v1_relat_1 @ X12))),
% 11.95/12.12      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.95/12.12  thf('3', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         (((k7_relat_1 @ sk_B_1 @ X0)
% 11.95/12.12            = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 11.95/12.12          | ~ (v1_relat_1 @ sk_B_1))),
% 11.95/12.12      inference('sup+', [status(thm)], ['1', '2'])).
% 11.95/12.12  thf('4', plain, ((v1_relat_1 @ sk_B_1)),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('5', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         ((k7_relat_1 @ sk_B_1 @ X0)
% 11.95/12.12           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.12      inference('demod', [status(thm)], ['3', '4'])).
% 11.95/12.12  thf(d3_tarski, axiom,
% 11.95/12.12    (![A:$i,B:$i]:
% 11.95/12.12     ( ( r1_tarski @ A @ B ) <=>
% 11.95/12.12       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 11.95/12.12  thf('6', plain,
% 11.95/12.12      (![X3 : $i, X5 : $i]:
% 11.95/12.12         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 11.95/12.12      inference('cnf', [status(esa)], [d3_tarski])).
% 11.95/12.12  thf(t86_relat_1, axiom,
% 11.95/12.12    (![A:$i,B:$i,C:$i]:
% 11.95/12.12     ( ( v1_relat_1 @ C ) =>
% 11.95/12.12       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 11.95/12.12         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 11.95/12.12  thf('7', plain,
% 11.95/12.12      (![X14 : $i, X15 : $i, X16 : $i]:
% 11.95/12.12         (~ (r2_hidden @ X14 @ (k1_relat_1 @ (k7_relat_1 @ X16 @ X15)))
% 11.95/12.12          | (r2_hidden @ X14 @ (k1_relat_1 @ X16))
% 11.95/12.12          | ~ (v1_relat_1 @ X16))),
% 11.95/12.12      inference('cnf', [status(esa)], [t86_relat_1])).
% 11.95/12.12  thf('8', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.95/12.12         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 11.95/12.12          | ~ (v1_relat_1 @ X1)
% 11.95/12.12          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 11.95/12.12             (k1_relat_1 @ X1)))),
% 11.95/12.12      inference('sup-', [status(thm)], ['6', '7'])).
% 11.95/12.12  thf('9', plain,
% 11.95/12.12      (![X3 : $i, X5 : $i]:
% 11.95/12.12         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 11.95/12.12      inference('cnf', [status(esa)], [d3_tarski])).
% 11.95/12.12  thf('10', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i]:
% 11.95/12.12         (~ (v1_relat_1 @ X0)
% 11.95/12.12          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 11.95/12.12             (k1_relat_1 @ X0))
% 11.95/12.12          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 11.95/12.12             (k1_relat_1 @ X0)))),
% 11.95/12.12      inference('sup-', [status(thm)], ['8', '9'])).
% 11.95/12.12  thf('11', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i]:
% 11.95/12.12         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 11.95/12.12           (k1_relat_1 @ X0))
% 11.95/12.12          | ~ (v1_relat_1 @ X0))),
% 11.95/12.12      inference('simplify', [status(thm)], ['10'])).
% 11.95/12.12  thf('12', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ 
% 11.95/12.12           (k1_relat_1 @ sk_B_1))
% 11.95/12.12          | ~ (v1_relat_1 @ sk_B_1))),
% 11.95/12.12      inference('sup+', [status(thm)], ['5', '11'])).
% 11.95/12.12  thf('13', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('15', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ 
% 11.95/12.12          (k1_relat_1 @ sk_A))),
% 11.95/12.12      inference('demod', [status(thm)], ['12', '13', '14'])).
% 11.95/12.12  thf(t165_funct_1, axiom,
% 11.95/12.12    (![A:$i]:
% 11.95/12.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 11.95/12.12       ( ![B:$i]:
% 11.95/12.12         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 11.95/12.12           ( ![C:$i]:
% 11.95/12.12             ( ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 11.95/12.12                 ( r1_tarski @ C @ ( k1_relat_1 @ B ) ) ) =>
% 11.95/12.12               ( ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) <=>
% 11.95/12.12                 ( ![D:$i]:
% 11.95/12.12                   ( ( r2_hidden @ D @ C ) =>
% 11.95/12.12                     ( ( k1_funct_1 @ A @ D ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 11.95/12.12  thf('16', plain,
% 11.95/12.12      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.95/12.12         (~ (v1_relat_1 @ X21)
% 11.95/12.12          | ~ (v1_funct_1 @ X21)
% 11.95/12.12          | (r2_hidden @ (sk_D @ X22 @ X21 @ X23) @ X22)
% 11.95/12.12          | ((k7_relat_1 @ X23 @ X22) = (k7_relat_1 @ X21 @ X22))
% 11.95/12.12          | ~ (r1_tarski @ X22 @ (k1_relat_1 @ X21))
% 11.95/12.12          | ~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 11.95/12.12          | ~ (v1_funct_1 @ X23)
% 11.95/12.12          | ~ (v1_relat_1 @ X23))),
% 11.95/12.12      inference('cnf', [status(esa)], [t165_funct_1])).
% 11.95/12.12  thf('17', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i]:
% 11.95/12.12         (~ (v1_relat_1 @ X1)
% 11.95/12.12          | ~ (v1_funct_1 @ X1)
% 11.95/12.12          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ 
% 11.95/12.12               (k1_relat_1 @ X1))
% 11.95/12.12          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))
% 11.95/12.12              = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))
% 11.95/12.12          | (r2_hidden @ 
% 11.95/12.12             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ sk_A @ X1) @ 
% 11.95/12.12             (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))
% 11.95/12.12          | ~ (v1_funct_1 @ sk_A)
% 11.95/12.12          | ~ (v1_relat_1 @ sk_A))),
% 11.95/12.12      inference('sup-', [status(thm)], ['15', '16'])).
% 11.95/12.12  thf(commutativity_k3_xboole_0, axiom,
% 11.95/12.12    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 11.95/12.12  thf('18', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.95/12.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.95/12.12  thf('19', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         ((k7_relat_1 @ sk_B_1 @ X0)
% 11.95/12.12           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.12      inference('demod', [status(thm)], ['3', '4'])).
% 11.95/12.12  thf('20', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         ((k7_relat_1 @ sk_B_1 @ X0)
% 11.95/12.12           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))),
% 11.95/12.12      inference('sup+', [status(thm)], ['18', '19'])).
% 11.95/12.12  thf(t90_relat_1, axiom,
% 11.95/12.12    (![A:$i,B:$i]:
% 11.95/12.12     ( ( v1_relat_1 @ B ) =>
% 11.95/12.12       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 11.95/12.12         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 11.95/12.12  thf('21', plain,
% 11.95/12.12      (![X17 : $i, X18 : $i]:
% 11.95/12.12         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 11.95/12.12            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 11.95/12.12          | ~ (v1_relat_1 @ X17))),
% 11.95/12.12      inference('cnf', [status(esa)], [t90_relat_1])).
% 11.95/12.12  thf('22', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         (((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.12            = (k3_xboole_0 @ (k1_relat_1 @ sk_B_1) @ 
% 11.95/12.12               (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))
% 11.95/12.12          | ~ (v1_relat_1 @ sk_B_1))),
% 11.95/12.12      inference('sup+', [status(thm)], ['20', '21'])).
% 11.95/12.12  thf('23', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('25', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.12           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.12              (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))),
% 11.95/12.12      inference('demod', [status(thm)], ['22', '23', '24'])).
% 11.95/12.12  thf('26', plain,
% 11.95/12.12      (![X12 : $i, X13 : $i]:
% 11.95/12.12         (((k7_relat_1 @ X12 @ X13)
% 11.95/12.12            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13)))
% 11.95/12.12          | ~ (v1_relat_1 @ X12))),
% 11.95/12.12      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.95/12.12  thf('27', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         (((k7_relat_1 @ sk_A @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A)))
% 11.95/12.12            = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))
% 11.95/12.12          | ~ (v1_relat_1 @ sk_A))),
% 11.95/12.12      inference('sup+', [status(thm)], ['25', '26'])).
% 11.95/12.12  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('29', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         ((k7_relat_1 @ sk_A @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A)))
% 11.95/12.12           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))),
% 11.95/12.12      inference('demod', [status(thm)], ['27', '28'])).
% 11.95/12.12  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('32', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i]:
% 11.95/12.12         (~ (v1_relat_1 @ X1)
% 11.95/12.12          | ~ (v1_funct_1 @ X1)
% 11.95/12.12          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ 
% 11.95/12.12               (k1_relat_1 @ X1))
% 11.95/12.12          | ((k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))
% 11.95/12.12              = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))
% 11.95/12.12          | (r2_hidden @ 
% 11.95/12.12             (sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)) @ sk_A @ X1) @ 
% 11.95/12.12             (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))),
% 11.95/12.12      inference('demod', [status(thm)], ['17', '29', '30', '31'])).
% 11.95/12.12  thf('33', plain,
% 11.95/12.12      (![X12 : $i, X13 : $i]:
% 11.95/12.12         (((k7_relat_1 @ X12 @ X13)
% 11.95/12.12            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13)))
% 11.95/12.12          | ~ (v1_relat_1 @ X12))),
% 11.95/12.12      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.95/12.12  thf('34', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         ((k7_relat_1 @ sk_B_1 @ X0)
% 11.95/12.12           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.12      inference('demod', [status(thm)], ['3', '4'])).
% 11.95/12.12  thf('35', plain,
% 11.95/12.12      (![X17 : $i, X18 : $i]:
% 11.95/12.12         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 11.95/12.12            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 11.95/12.13          | ~ (v1_relat_1 @ X17))),
% 11.95/12.13      inference('cnf', [status(esa)], [t90_relat_1])).
% 11.95/12.13  thf('36', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ sk_B_1) @ 
% 11.95/12.13               (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 11.95/12.13          | ~ (v1_relat_1 @ sk_B_1))),
% 11.95/12.13      inference('sup+', [status(thm)], ['34', '35'])).
% 11.95/12.13  thf('37', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('38', plain, ((v1_relat_1 @ sk_B_1)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('39', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.13           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13              (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['36', '37', '38'])).
% 11.95/12.13  thf('40', plain,
% 11.95/12.13      (![X12 : $i, X13 : $i]:
% 11.95/12.13         (((k7_relat_1 @ X12 @ X13)
% 11.95/12.13            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13)))
% 11.95/12.13          | ~ (v1_relat_1 @ X12))),
% 11.95/12.13      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.95/12.13  thf('41', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 11.95/12.13            = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))
% 11.95/12.13          | ~ (v1_relat_1 @ sk_A))),
% 11.95/12.13      inference('sup+', [status(thm)], ['39', '40'])).
% 11.95/12.13  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('43', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 11.95/12.13           = (k7_relat_1 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))),
% 11.95/12.13      inference('demod', [status(thm)], ['41', '42'])).
% 11.95/12.13  thf('44', plain,
% 11.95/12.13      (![X17 : $i, X18 : $i]:
% 11.95/12.13         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 11.95/12.13          | ~ (v1_relat_1 @ X17))),
% 11.95/12.13      inference('cnf', [status(esa)], [t90_relat_1])).
% 11.95/12.13  thf('45', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k1_relat_1 @ 
% 11.95/12.13            (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13               (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))
% 11.95/12.13          | ~ (v1_relat_1 @ sk_A))),
% 11.95/12.13      inference('sup+', [status(thm)], ['43', '44'])).
% 11.95/12.13  thf('46', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.13           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13              (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['36', '37', '38'])).
% 11.95/12.13  thf('47', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.13           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13              (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['36', '37', '38'])).
% 11.95/12.13  thf('48', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ 
% 11.95/12.13           (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 11.95/12.13           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13              (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))),
% 11.95/12.13      inference('sup+', [status(thm)], ['46', '47'])).
% 11.95/12.13  thf('49', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k7_relat_1 @ sk_B_1 @ X0)
% 11.95/12.13           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['3', '4'])).
% 11.95/12.13  thf('50', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.13           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13              (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))),
% 11.95/12.13      inference('demod', [status(thm)], ['48', '49'])).
% 11.95/12.13  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('52', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ 
% 11.95/12.13           (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['45', '50', '51'])).
% 11.95/12.13  thf('53', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 11.95/12.13            = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))
% 11.95/12.13          | ~ (v1_relat_1 @ sk_A))),
% 11.95/12.13      inference('sup+', [status(thm)], ['33', '52'])).
% 11.95/12.13  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('55', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['53', '54'])).
% 11.95/12.13  thf('56', plain,
% 11.95/12.13      (![X17 : $i, X18 : $i]:
% 11.95/12.13         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 11.95/12.13          | ~ (v1_relat_1 @ X17))),
% 11.95/12.13      inference('cnf', [status(esa)], [t90_relat_1])).
% 11.95/12.13  thf('57', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['53', '54'])).
% 11.95/12.13  thf('58', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ sk_B_1) @ X0))
% 11.95/12.13          | ~ (v1_relat_1 @ sk_B_1))),
% 11.95/12.13      inference('sup+', [status(thm)], ['56', '57'])).
% 11.95/12.13  thf('59', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('60', plain, ((v1_relat_1 @ sk_B_1)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('61', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_A @ X0))
% 11.95/12.13           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))),
% 11.95/12.13      inference('demod', [status(thm)], ['58', '59', '60'])).
% 11.95/12.13  thf('62', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['55', '61'])).
% 11.95/12.13  thf('63', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['55', '61'])).
% 11.95/12.13  thf('64', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.95/12.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.95/12.13  thf(s3_funct_1__e9_44_1__funct_1, axiom,
% 11.95/12.13    (![A:$i]:
% 11.95/12.13     ( ?[B:$i]:
% 11.95/12.13       ( ( ![C:$i]:
% 11.95/12.13           ( ( r2_hidden @ C @ A ) =>
% 11.95/12.13             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 11.95/12.13         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 11.95/12.13         ( v1_relat_1 @ B ) ) ))).
% 11.95/12.13  thf('65', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B @ X19)) = (X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf(t189_relat_1, axiom,
% 11.95/12.13    (![A:$i]:
% 11.95/12.13     ( ( v1_relat_1 @ A ) =>
% 11.95/12.13       ( ![B:$i]:
% 11.95/12.13         ( ( v1_relat_1 @ B ) =>
% 11.95/12.13           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 11.95/12.13             ( k7_relat_1 @
% 11.95/12.13               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 11.95/12.13  thf('66', plain,
% 11.95/12.13      (![X10 : $i, X11 : $i]:
% 11.95/12.13         (~ (v1_relat_1 @ X10)
% 11.95/12.13          | ((k7_relat_1 @ X11 @ (k1_relat_1 @ X10))
% 11.95/12.13              = (k7_relat_1 @ X11 @ 
% 11.95/12.13                 (k1_relat_1 @ (k7_relat_1 @ X10 @ (k1_relat_1 @ X11)))))
% 11.95/12.13          | ~ (v1_relat_1 @ X11))),
% 11.95/12.13      inference('cnf', [status(esa)], [t189_relat_1])).
% 11.95/12.13  thf('67', plain,
% 11.95/12.13      (![X10 : $i, X11 : $i]:
% 11.95/12.13         (~ (v1_relat_1 @ X10)
% 11.95/12.13          | ((k7_relat_1 @ X11 @ (k1_relat_1 @ X10))
% 11.95/12.13              = (k7_relat_1 @ X11 @ 
% 11.95/12.13                 (k1_relat_1 @ (k7_relat_1 @ X10 @ (k1_relat_1 @ X11)))))
% 11.95/12.13          | ~ (v1_relat_1 @ X11))),
% 11.95/12.13      inference('cnf', [status(esa)], [t189_relat_1])).
% 11.95/12.13  thf('68', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.13           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13              (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))),
% 11.95/12.13      inference('demod', [status(thm)], ['48', '49'])).
% 11.95/12.13  thf('69', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k1_relat_1 @ 
% 11.95/12.13            (k7_relat_1 @ sk_B_1 @ 
% 11.95/12.13             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_B_1)))))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13               (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ (k1_relat_1 @ X0)))))
% 11.95/12.13          | ~ (v1_relat_1 @ sk_B_1)
% 11.95/12.13          | ~ (v1_relat_1 @ X0))),
% 11.95/12.13      inference('sup+', [status(thm)], ['67', '68'])).
% 11.95/12.13  thf('70', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('71', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))
% 11.95/12.13           = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13              (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0))))),
% 11.95/12.13      inference('demod', [status(thm)], ['48', '49'])).
% 11.95/12.13  thf('72', plain, ((v1_relat_1 @ sk_B_1)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('73', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k1_relat_1 @ 
% 11.95/12.13            (k7_relat_1 @ sk_B_1 @ 
% 11.95/12.13             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A)))))
% 11.95/12.13            = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ (k1_relat_1 @ X0))))
% 11.95/12.13          | ~ (v1_relat_1 @ X0))),
% 11.95/12.13      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 11.95/12.13  thf('74', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['55', '61'])).
% 11.95/12.13  thf('75', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['55', '61'])).
% 11.95/12.13  thf('76', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 11.95/12.13            (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A))))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ X0)))
% 11.95/12.13          | ~ (v1_relat_1 @ X0))),
% 11.95/12.13      inference('demod', [status(thm)], ['73', '74', '75'])).
% 11.95/12.13  thf('77', plain,
% 11.95/12.13      (![X12 : $i, X13 : $i]:
% 11.95/12.13         (((k7_relat_1 @ X12 @ X13)
% 11.95/12.13            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13)))
% 11.95/12.13          | ~ (v1_relat_1 @ X12))),
% 11.95/12.13      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.95/12.13  thf('78', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k7_relat_1 @ sk_A @ 
% 11.95/12.13            (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A))))
% 11.95/12.13            = (k7_relat_1 @ sk_A @ 
% 11.95/12.13               (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ X0))))
% 11.95/12.13          | ~ (v1_relat_1 @ X0)
% 11.95/12.13          | ~ (v1_relat_1 @ sk_A))),
% 11.95/12.13      inference('sup+', [status(thm)], ['76', '77'])).
% 11.95/12.13  thf('79', plain, ((v1_relat_1 @ sk_A)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('80', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k7_relat_1 @ sk_A @ 
% 11.95/12.13            (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_A))))
% 11.95/12.13            = (k7_relat_1 @ sk_A @ 
% 11.95/12.13               (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ X0))))
% 11.95/12.13          | ~ (v1_relat_1 @ X0))),
% 11.95/12.13      inference('demod', [status(thm)], ['78', '79'])).
% 11.95/12.13  thf('81', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k7_relat_1 @ sk_A @ (k1_relat_1 @ X0))
% 11.95/12.13            = (k7_relat_1 @ sk_A @ 
% 11.95/12.13               (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ X0))))
% 11.95/12.13          | ~ (v1_relat_1 @ sk_A)
% 11.95/12.13          | ~ (v1_relat_1 @ X0)
% 11.95/12.13          | ~ (v1_relat_1 @ X0))),
% 11.95/12.13      inference('sup+', [status(thm)], ['66', '80'])).
% 11.95/12.13  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('83', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k7_relat_1 @ sk_A @ (k1_relat_1 @ X0))
% 11.95/12.13            = (k7_relat_1 @ sk_A @ 
% 11.95/12.13               (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ X0))))
% 11.95/12.13          | ~ (v1_relat_1 @ X0)
% 11.95/12.13          | ~ (v1_relat_1 @ X0))),
% 11.95/12.13      inference('demod', [status(thm)], ['81', '82'])).
% 11.95/12.13  thf('84', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (~ (v1_relat_1 @ X0)
% 11.95/12.13          | ((k7_relat_1 @ sk_A @ (k1_relat_1 @ X0))
% 11.95/12.13              = (k7_relat_1 @ sk_A @ 
% 11.95/12.13                 (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ X0)))))),
% 11.95/12.13      inference('simplify', [status(thm)], ['83'])).
% 11.95/12.13  thf('85', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k7_relat_1 @ sk_A @ (k1_relat_1 @ (sk_B @ X0)))
% 11.95/12.13            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))
% 11.95/12.13          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 11.95/12.13      inference('sup+', [status(thm)], ['65', '84'])).
% 11.95/12.13  thf('86', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B @ X19)) = (X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('87', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B @ X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('88', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k7_relat_1 @ sk_A @ X0)
% 11.95/12.13           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['85', '86', '87'])).
% 11.95/12.13  thf('89', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k7_relat_1 @ sk_A @ X0)
% 11.95/12.13           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))),
% 11.95/12.13      inference('sup+', [status(thm)], ['64', '88'])).
% 11.95/12.13  thf('90', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['55', '61'])).
% 11.95/12.13  thf('91', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)
% 11.95/12.13           = (k1_relat_1 @ (k7_relat_1 @ sk_B_1 @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['55', '61'])).
% 11.95/12.13  thf('92', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]:
% 11.95/12.13         (~ (v1_relat_1 @ X1)
% 11.95/12.13          | ~ (v1_funct_1 @ X1)
% 11.95/12.13          | ~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 11.95/12.13               (k1_relat_1 @ X1))
% 11.95/12.13          | ((k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 11.95/12.13              = (k7_relat_1 @ sk_A @ X0))
% 11.95/12.13          | (r2_hidden @ 
% 11.95/12.13             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ X1) @ 
% 11.95/12.13             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['32', '62', '63', '89', '90', '91'])).
% 11.95/12.13  thf('93', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 11.95/12.13             (k1_relat_1 @ sk_A))
% 11.95/12.13          | (r2_hidden @ 
% 11.95/12.13             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B_1) @ 
% 11.95/12.13             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 11.95/12.13          | ((k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 11.95/12.13              = (k7_relat_1 @ sk_A @ X0))
% 11.95/12.13          | ~ (v1_funct_1 @ sk_B_1)
% 11.95/12.13          | ~ (v1_relat_1 @ sk_B_1))),
% 11.95/12.13      inference('sup-', [status(thm)], ['0', '92'])).
% 11.95/12.13  thf('94', plain,
% 11.95/12.13      (![X17 : $i, X18 : $i]:
% 11.95/12.13         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 11.95/12.13          | ~ (v1_relat_1 @ X17))),
% 11.95/12.13      inference('cnf', [status(esa)], [t90_relat_1])).
% 11.95/12.13  thf('95', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B @ X19)) = (X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('96', plain,
% 11.95/12.13      (![X12 : $i, X13 : $i]:
% 11.95/12.13         (((k7_relat_1 @ X12 @ X13)
% 11.95/12.13            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13)))
% 11.95/12.13          | ~ (v1_relat_1 @ X12))),
% 11.95/12.13      inference('cnf', [status(esa)], [t192_relat_1])).
% 11.95/12.13  thf('97', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]:
% 11.95/12.13         (((k7_relat_1 @ (sk_B @ X0) @ X1)
% 11.95/12.13            = (k7_relat_1 @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 11.95/12.13          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 11.95/12.13      inference('sup+', [status(thm)], ['95', '96'])).
% 11.95/12.13  thf('98', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B @ X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('99', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]:
% 11.95/12.13         ((k7_relat_1 @ (sk_B @ X0) @ X1)
% 11.95/12.13           = (k7_relat_1 @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 11.95/12.13      inference('demod', [status(thm)], ['97', '98'])).
% 11.95/12.13  thf('100', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]:
% 11.95/12.13         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 11.95/12.13           (k1_relat_1 @ X0))
% 11.95/12.13          | ~ (v1_relat_1 @ X0))),
% 11.95/12.13      inference('simplify', [status(thm)], ['10'])).
% 11.95/12.13  thf('101', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]:
% 11.95/12.13         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ X0)) @ 
% 11.95/12.13           (k1_relat_1 @ (sk_B @ X1)))
% 11.95/12.13          | ~ (v1_relat_1 @ (sk_B @ X1)))),
% 11.95/12.13      inference('sup+', [status(thm)], ['99', '100'])).
% 11.95/12.13  thf('102', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B @ X19)) = (X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('103', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B @ X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('104', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]:
% 11.95/12.13         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (sk_B @ X1) @ X0)) @ X1)),
% 11.95/12.13      inference('demod', [status(thm)], ['101', '102', '103'])).
% 11.95/12.13  thf('105', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]:
% 11.95/12.13         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ (sk_B @ X1)) @ X0) @ X1)
% 11.95/12.13          | ~ (v1_relat_1 @ (sk_B @ X1)))),
% 11.95/12.13      inference('sup+', [status(thm)], ['94', '104'])).
% 11.95/12.13  thf('106', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B @ X19)) = (X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('107', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B @ X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('108', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 11.95/12.13      inference('demod', [status(thm)], ['105', '106', '107'])).
% 11.95/12.13  thf('109', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k7_relat_1 @ sk_B_1 @ X0)
% 11.95/12.13           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['3', '4'])).
% 11.95/12.13  thf('110', plain, ((v1_funct_1 @ sk_B_1)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('111', plain, ((v1_relat_1 @ sk_B_1)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('112', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((r2_hidden @ 
% 11.95/12.13           (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B_1) @ 
% 11.95/12.13           (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0))
% 11.95/12.13          | ((k7_relat_1 @ sk_B_1 @ X0) = (k7_relat_1 @ sk_A @ X0)))),
% 11.95/12.13      inference('demod', [status(thm)], ['93', '108', '109', '110', '111'])).
% 11.95/12.13  thf('113', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B @ X19)) = (X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('114', plain,
% 11.95/12.13      (![X17 : $i, X18 : $i]:
% 11.95/12.13         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 11.95/12.13            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 11.95/12.13          | ~ (v1_relat_1 @ X17))),
% 11.95/12.13      inference('cnf', [status(esa)], [t90_relat_1])).
% 11.95/12.13  thf('115', plain,
% 11.95/12.13      (![X14 : $i, X15 : $i, X16 : $i]:
% 11.95/12.13         (~ (r2_hidden @ X14 @ (k1_relat_1 @ (k7_relat_1 @ X16 @ X15)))
% 11.95/12.13          | (r2_hidden @ X14 @ X15)
% 11.95/12.13          | ~ (v1_relat_1 @ X16))),
% 11.95/12.13      inference('cnf', [status(esa)], [t86_relat_1])).
% 11.95/12.13  thf('116', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.95/12.13         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 11.95/12.13          | ~ (v1_relat_1 @ X1)
% 11.95/12.13          | ~ (v1_relat_1 @ X1)
% 11.95/12.13          | (r2_hidden @ X2 @ X0))),
% 11.95/12.13      inference('sup-', [status(thm)], ['114', '115'])).
% 11.95/12.13  thf('117', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.95/12.13         ((r2_hidden @ X2 @ X0)
% 11.95/12.13          | ~ (v1_relat_1 @ X1)
% 11.95/12.13          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 11.95/12.13      inference('simplify', [status(thm)], ['116'])).
% 11.95/12.13  thf('118', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.95/12.13         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1))
% 11.95/12.13          | ~ (v1_relat_1 @ (sk_B @ X0))
% 11.95/12.13          | (r2_hidden @ X2 @ X1))),
% 11.95/12.13      inference('sup-', [status(thm)], ['113', '117'])).
% 11.95/12.13  thf('119', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B @ X19))),
% 11.95/12.13      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 11.95/12.13  thf('120', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.95/12.13         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)) | (r2_hidden @ X2 @ X1))),
% 11.95/12.13      inference('demod', [status(thm)], ['118', '119'])).
% 11.95/12.13  thf('121', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         (((k7_relat_1 @ sk_B_1 @ X0) = (k7_relat_1 @ sk_A @ X0))
% 11.95/12.13          | (r2_hidden @ 
% 11.95/12.13             (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ sk_A @ sk_B_1) @ 
% 11.95/12.13             X0))),
% 11.95/12.13      inference('sup-', [status(thm)], ['112', '120'])).
% 11.95/12.13  thf('122', plain,
% 11.95/12.13      (![X25 : $i]:
% 11.95/12.13         (((k1_funct_1 @ sk_A @ X25) = (k1_funct_1 @ sk_B_1 @ X25))
% 11.95/12.13          | ~ (r2_hidden @ X25 @ sk_C_1))),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('123', plain,
% 11.95/12.13      ((((k7_relat_1 @ sk_B_1 @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1))
% 11.95/12.13        | ((k1_funct_1 @ sk_A @ 
% 11.95/12.13            (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 11.95/12.13             sk_B_1))
% 11.95/12.13            = (k1_funct_1 @ sk_B_1 @ 
% 11.95/12.13               (sk_D @ (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 11.95/12.13                sk_B_1))))),
% 11.95/12.13      inference('sup-', [status(thm)], ['121', '122'])).
% 11.95/12.13  thf('124', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.95/12.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.95/12.13  thf('125', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.95/12.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.95/12.13  thf('126', plain,
% 11.95/12.13      ((((k7_relat_1 @ sk_B_1 @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1))
% 11.95/12.13        | ((k1_funct_1 @ sk_A @ 
% 11.95/12.13            (sk_D @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ sk_A @ 
% 11.95/12.13             sk_B_1))
% 11.95/12.13            = (k1_funct_1 @ sk_B_1 @ 
% 11.95/12.13               (sk_D @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ sk_A @ 
% 11.95/12.13                sk_B_1))))),
% 11.95/12.13      inference('demod', [status(thm)], ['123', '124', '125'])).
% 11.95/12.13  thf('127', plain,
% 11.95/12.13      (((k7_relat_1 @ sk_A @ sk_C_1) != (k7_relat_1 @ sk_B_1 @ sk_C_1))),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('128', plain,
% 11.95/12.13      (((k1_funct_1 @ sk_A @ 
% 11.95/12.13         (sk_D @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ sk_A @ sk_B_1))
% 11.95/12.13         = (k1_funct_1 @ sk_B_1 @ 
% 11.95/12.13            (sk_D @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ sk_A @ 
% 11.95/12.13             sk_B_1)))),
% 11.95/12.13      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 11.95/12.13  thf('129', plain,
% 11.95/12.13      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.95/12.13         (~ (v1_relat_1 @ X21)
% 11.95/12.13          | ~ (v1_funct_1 @ X21)
% 11.95/12.13          | ((k1_funct_1 @ X23 @ (sk_D @ X22 @ X21 @ X23))
% 11.95/12.13              != (k1_funct_1 @ X21 @ (sk_D @ X22 @ X21 @ X23)))
% 11.95/12.13          | ((k7_relat_1 @ X23 @ X22) = (k7_relat_1 @ X21 @ X22))
% 11.95/12.13          | ~ (r1_tarski @ X22 @ (k1_relat_1 @ X21))
% 11.95/12.13          | ~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 11.95/12.13          | ~ (v1_funct_1 @ X23)
% 11.95/12.13          | ~ (v1_relat_1 @ X23))),
% 11.95/12.13      inference('cnf', [status(esa)], [t165_funct_1])).
% 11.95/12.13  thf('130', plain,
% 11.95/12.13      ((((k1_funct_1 @ sk_A @ 
% 11.95/12.13          (sk_D @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ sk_A @ sk_B_1))
% 11.95/12.13          != (k1_funct_1 @ sk_A @ 
% 11.95/12.13              (sk_D @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ sk_A @ 
% 11.95/12.13               sk_B_1)))
% 11.95/12.13        | ~ (v1_relat_1 @ sk_B_1)
% 11.95/12.13        | ~ (v1_funct_1 @ sk_B_1)
% 11.95/12.13        | ~ (r1_tarski @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ 
% 11.95/12.13             (k1_relat_1 @ sk_B_1))
% 11.95/12.13        | ~ (r1_tarski @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ 
% 11.95/12.13             (k1_relat_1 @ sk_A))
% 11.95/12.13        | ((k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 11.95/12.13            = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 11.95/12.13        | ~ (v1_funct_1 @ sk_A)
% 11.95/12.13        | ~ (v1_relat_1 @ sk_A))),
% 11.95/12.13      inference('sup-', [status(thm)], ['128', '129'])).
% 11.95/12.13  thf('131', plain, ((v1_relat_1 @ sk_B_1)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('132', plain, ((v1_funct_1 @ sk_B_1)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('133', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('134', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 11.95/12.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.95/12.13  thf('135', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 11.95/12.13      inference('demod', [status(thm)], ['105', '106', '107'])).
% 11.95/12.13  thf('136', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 11.95/12.13      inference('sup+', [status(thm)], ['134', '135'])).
% 11.95/12.13  thf('137', plain,
% 11.95/12.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 11.95/12.13      inference('sup+', [status(thm)], ['134', '135'])).
% 11.95/12.13  thf('138', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k7_relat_1 @ sk_B_1 @ X0)
% 11.95/12.13           = (k7_relat_1 @ sk_B_1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))),
% 11.95/12.13      inference('sup+', [status(thm)], ['18', '19'])).
% 11.95/12.13  thf('139', plain,
% 11.95/12.13      (![X0 : $i]:
% 11.95/12.13         ((k7_relat_1 @ sk_A @ X0)
% 11.95/12.13           = (k7_relat_1 @ sk_A @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_A))))),
% 11.95/12.13      inference('sup+', [status(thm)], ['64', '88'])).
% 11.95/12.13  thf('140', plain, ((v1_funct_1 @ sk_A)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('141', plain, ((v1_relat_1 @ sk_A)),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('142', plain,
% 11.95/12.13      ((((k1_funct_1 @ sk_A @ 
% 11.95/12.13          (sk_D @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ sk_A @ sk_B_1))
% 11.95/12.13          != (k1_funct_1 @ sk_A @ 
% 11.95/12.13              (sk_D @ (k3_xboole_0 @ sk_C_1 @ (k1_relat_1 @ sk_A)) @ sk_A @ 
% 11.95/12.13               sk_B_1)))
% 11.95/12.13        | ((k7_relat_1 @ sk_B_1 @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1)))),
% 11.95/12.13      inference('demod', [status(thm)],
% 11.95/12.13                ['130', '131', '132', '133', '136', '137', '138', '139', 
% 11.95/12.13                 '140', '141'])).
% 11.95/12.13  thf('143', plain,
% 11.95/12.13      (((k7_relat_1 @ sk_B_1 @ sk_C_1) = (k7_relat_1 @ sk_A @ sk_C_1))),
% 11.95/12.13      inference('simplify', [status(thm)], ['142'])).
% 11.95/12.13  thf('144', plain,
% 11.95/12.13      (((k7_relat_1 @ sk_A @ sk_C_1) != (k7_relat_1 @ sk_B_1 @ sk_C_1))),
% 11.95/12.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.13  thf('145', plain, ($false),
% 11.95/12.13      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 11.95/12.13  
% 11.95/12.13  % SZS output end Refutation
% 11.95/12.13  
% 11.95/12.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
