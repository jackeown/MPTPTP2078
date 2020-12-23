%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0621+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uVj8mx1Y4D

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  407 ( 722 expanded)
%              Number of equality atoms :   67 ( 129 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_16_type,type,(
    sk_B_16: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_7_type,type,(
    sk_A_7: $i )).

thf(sk_C_39_type,type,(
    sk_C_39: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X436: $i,X437: $i,X438: $i] :
      ( ( X437 != X436 )
      | ( r2_hidden @ ( X437 @ X438 ) )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X436: $i] :
      ( r2_hidden @ ( X436 @ ( k1_tarski @ X436 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X2640: $i,X2641: $i] :
      ( ( v1_relat_1 @ ( sk_C_39 @ ( X2640 @ X2641 ) ) )
      | ( X2641 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X2640: $i,X2641: $i] :
      ( ( v1_relat_1 @ ( sk_C_39 @ ( X2640 @ X2641 ) ) )
      | ( X2641 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X2640: $i,X2641: $i] :
      ( ( v1_funct_1 @ ( sk_C_39 @ ( X2640 @ X2641 ) ) )
      | ( X2641 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X2640: $i,X2641: $i] :
      ( ( v1_funct_1 @ ( sk_C_39 @ ( X2640 @ X2641 ) ) )
      | ( X2641 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2640: $i,X2641: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_39 @ ( X2640 @ X2641 ) ) )
        = X2641 )
      | ( X2641 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X2640: $i,X2641: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_39 @ ( X2640 @ X2641 ) ) )
        = X2641 )
      | ( X2641 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( ( k1_funct_1 @ ( B @ C ) )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('11',plain,(
    ! [X2632: $i] :
      ( ( k1_relat_1 @ ( sk_B_16 @ X2632 ) )
      = X2632 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('12',plain,(
    ! [X2642: $i,X2643: $i] :
      ( ~ ( v1_relat_1 @ X2642 )
      | ~ ( v1_funct_1 @ X2642 )
      | ( X2643 = X2642 )
      | ( ( k1_relat_1 @ X2642 )
       != sk_A_7 )
      | ( ( k1_relat_1 @ X2643 )
       != sk_A_7 )
      | ~ ( v1_funct_1 @ X2643 )
      | ~ ( v1_relat_1 @ X2643 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A_7 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A_7 )
      | ( X1
        = ( sk_B_16 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_16 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_16 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2632: $i] :
      ( v1_funct_1 @ ( sk_B_16 @ X2632 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('15',plain,(
    ! [X2632: $i] :
      ( v1_relat_1 @ ( sk_B_16 @ X2632 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A_7 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A_7 )
      | ( X1
        = ( sk_B_16 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_16 @ sk_A_7 ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A_7 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A_7 )
      | ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_39 @ ( X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_39 @ ( X1 @ X0 ) ) )
      | ( ( sk_C_39 @ ( X1 @ X0 ) )
        = ( sk_B_16 @ sk_A_7 ) ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( ( sk_C_39 @ ( X1 @ sk_A_7 ) )
        = ( sk_B_16 @ sk_A_7 ) )
      | ~ ( v1_funct_1 @ ( sk_C_39 @ ( X1 @ sk_A_7 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_39 @ ( X1 @ sk_A_7 ) ) )
      | ( sk_A_7 = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    sk_A_7 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    sk_A_7 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( ( sk_C_39 @ ( X1 @ sk_A_7 ) )
        = ( sk_B_16 @ sk_A_7 ) )
      | ~ ( v1_funct_1 @ ( sk_C_39 @ ( X1 @ sk_A_7 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_39 @ ( X1 @ sk_A_7 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_A_7 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_39 @ ( X0 @ sk_A_7 ) ) )
      | ( ( sk_C_39 @ ( X0 @ sk_A_7 ) )
        = ( sk_B_16 @ sk_A_7 ) ) ) ),
    inference('sup-',[status(thm)],['7','23'])).

thf('25',plain,(
    sk_A_7 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_39 @ ( X0 @ sk_A_7 ) ) )
      | ( ( sk_C_39 @ ( X0 @ sk_A_7 ) )
        = ( sk_B_16 @ sk_A_7 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_A_7 = o_0_0_xboole_0 )
      | ( ( sk_C_39 @ ( X0 @ sk_A_7 ) )
        = ( sk_B_16 @ sk_A_7 ) ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    sk_A_7 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_C_39 @ ( X0 @ sk_A_7 ) )
      = ( sk_B_16 @ sk_A_7 ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2640: $i,X2641: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_39 @ ( X2640 @ X2641 ) ) )
        = ( k1_tarski @ X2640 ) )
      | ( X2641 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
    ! [X2640: $i,X2641: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_39 @ ( X2640 @ X2641 ) ) )
        = ( k1_tarski @ X2640 ) )
      | ( X2641 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( sk_B_16 @ sk_A_7 ) )
        = ( k1_tarski @ X0 ) )
      | ( sk_A_7 = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    sk_A_7 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( sk_B_16 @ sk_A_7 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X436: $i] :
      ( r2_hidden @ ( X436 @ ( k1_tarski @ X436 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X0 @ X1 ) )
      | ~ ( r2_hidden @ ( X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k2_relat_1 @ ( sk_B_16 @ sk_A_7 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    $false ),
    inference('sup-',[status(thm)],['1','39'])).

%------------------------------------------------------------------------------
