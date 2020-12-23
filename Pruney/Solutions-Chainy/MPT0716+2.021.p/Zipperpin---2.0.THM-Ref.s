%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UesPVMFQA2

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:22 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 433 expanded)
%              Number of leaves         :   23 ( 128 expanded)
%              Depth                    :   27
%              Number of atoms          : 1100 (6496 expanded)
%              Number of equality atoms :   31 (  73 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t171_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
            <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
              <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                  & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('19',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('21',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
        = sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['17','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

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

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ ( k1_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('31',plain,
    ( ( ( sk_C
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( sk_C != sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','36','37','38'])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['14','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','13','52'])).

thf('54',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('56',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf('59',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','13','52','58'])).

thf('60',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('67',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('68',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('72',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','13','52','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','73','74'])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['55','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('80',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('81',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['54','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UesPVMFQA2
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 117 iterations in 0.115s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(t171_funct_1, conjecture,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.57           ( ![C:$i]:
% 0.36/0.57             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.36/0.57               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.36/0.57                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i]:
% 0.36/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.57          ( ![B:$i]:
% 0.36/0.57            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.57              ( ![C:$i]:
% 0.36/0.57                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.36/0.57                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.36/0.57                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.36/0.57        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.36/0.57        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.36/0.57       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.36/0.57       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf(t44_relat_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( v1_relat_1 @ B ) =>
% 0.36/0.57           ( r1_tarski @
% 0.36/0.57             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (![X12 : $i, X13 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X12)
% 0.36/0.57          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 0.36/0.57             (k1_relat_1 @ X13))
% 0.36/0.57          | ~ (v1_relat_1 @ X13))),
% 0.36/0.57      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.36/0.57        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('split', [status(esa)], ['4'])).
% 0.36/0.57  thf(t1_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.57       ( r1_tarski @ A @ C ) ))).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.57          | ~ (r1_tarski @ X1 @ X2)
% 0.36/0.57          | (r1_tarski @ X0 @ X2))),
% 0.36/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      ((![X0 : $i]:
% 0.36/0.57          ((r1_tarski @ sk_C @ X0)
% 0.36/0.57           | ~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ sk_A)
% 0.36/0.57         | ~ (v1_relat_1 @ sk_B)
% 0.36/0.57         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['3', '7'])).
% 0.36/0.57  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.36/0.57         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.36/0.57       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.57  thf(t148_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ B ) =>
% 0.36/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i]:
% 0.36/0.57         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.36/0.57          | ~ (v1_relat_1 @ X10))),
% 0.36/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.57  thf(fc8_funct_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.57       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.36/0.57         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (![X20 : $i, X21 : $i]:
% 0.36/0.57         (~ (v1_funct_1 @ X20)
% 0.36/0.57          | ~ (v1_relat_1 @ X20)
% 0.36/0.57          | (v1_funct_1 @ (k7_relat_1 @ X20 @ X21)))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.36/0.57  thf(dt_k7_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (![X5 : $i, X6 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.36/0.57      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.36/0.57  thf(t112_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ B ) =>
% 0.36/0.57       ( ![C:$i]:
% 0.36/0.57         ( ( v1_relat_1 @ C ) =>
% 0.36/0.57           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.36/0.57             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X7)
% 0.36/0.57          | ((k7_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.36/0.57              = (k5_relat_1 @ (k7_relat_1 @ X8 @ X9) @ X7))
% 0.36/0.57          | ~ (v1_relat_1 @ X8))),
% 0.36/0.57      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.36/0.57  thf(dt_k5_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.36/0.57       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      (![X3 : $i, X4 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X3)
% 0.36/0.57          | ~ (v1_relat_1 @ X4)
% 0.36/0.57          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.36/0.57      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('split', [status(esa)], ['4'])).
% 0.36/0.57  thf(t91_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ B ) =>
% 0.36/0.57       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.57         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (![X18 : $i, X19 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.36/0.57          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 0.36/0.57          | ~ (v1_relat_1 @ X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.36/0.57         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.36/0.57             = (sk_C))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ sk_B)
% 0.36/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.36/0.57         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.36/0.57             = (sk_C))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['18', '21'])).
% 0.36/0.57  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.36/0.57          = (sk_C)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.36/0.57  thf('26', plain,
% 0.36/0.57      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.36/0.57           = (sk_C))
% 0.36/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.36/0.57         | ~ (v1_relat_1 @ sk_B)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['17', '25'])).
% 0.36/0.57  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.36/0.57          = (sk_C)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.36/0.57  thf(t27_funct_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.57           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.36/0.57             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (![X22 : $i, X23 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X22)
% 0.36/0.57          | ~ (v1_funct_1 @ X22)
% 0.36/0.57          | (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X23))
% 0.36/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X22 @ X23)) != (k1_relat_1 @ X22))
% 0.36/0.57          | ~ (v1_funct_1 @ X23)
% 0.36/0.57          | ~ (v1_relat_1 @ X23))),
% 0.36/0.57      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (((((sk_C) != (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 0.36/0.57         | ~ (v1_relat_1 @ sk_B)
% 0.36/0.57         | ~ (v1_funct_1 @ sk_B)
% 0.36/0.57         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.36/0.57            (k1_relat_1 @ sk_B))
% 0.36/0.57         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.36/0.57         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      (![X18 : $i, X19 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.36/0.57          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 0.36/0.57          | ~ (v1_relat_1 @ X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.36/0.57  thf('34', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ sk_A)
% 0.36/0.57         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.57  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('39', plain,
% 0.36/0.57      (((((sk_C) != (sk_C))
% 0.36/0.57         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.36/0.57            (k1_relat_1 @ sk_B))
% 0.36/0.57         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.36/0.57         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['31', '36', '37', '38'])).
% 0.36/0.57  thf('40', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.36/0.57         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.36/0.57         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.36/0.57            (k1_relat_1 @ sk_B))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.36/0.57  thf('41', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ sk_A)
% 0.36/0.57         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.36/0.57            (k1_relat_1 @ sk_B))
% 0.36/0.57         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['16', '40'])).
% 0.36/0.57  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      ((((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.36/0.57          (k1_relat_1 @ sk_B))
% 0.36/0.57         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ sk_A)
% 0.36/0.57         | ~ (v1_funct_1 @ sk_A)
% 0.36/0.57         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.36/0.57            (k1_relat_1 @ sk_B))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['15', '43'])).
% 0.36/0.57  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('46', plain, ((v1_funct_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('47', plain,
% 0.36/0.57      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.36/0.57         (k1_relat_1 @ sk_B)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.36/0.57         | ~ (v1_relat_1 @ sk_A)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['14', '47'])).
% 0.36/0.57  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.57  thf('51', plain,
% 0.36/0.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.36/0.57         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.36/0.57       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['2', '13', '52'])).
% 0.36/0.57  thf('54', plain,
% 0.36/0.57      (~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['1', '53'])).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      (![X5 : $i, X6 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.36/0.57      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.36/0.57        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('57', plain,
% 0.36/0.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.36/0.57         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.36/0.57      inference('split', [status(esa)], ['56'])).
% 0.36/0.57  thf('58', plain,
% 0.36/0.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))) | 
% 0.36/0.57       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('split', [status(esa)], ['56'])).
% 0.36/0.57  thf('59', plain,
% 0.36/0.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['2', '13', '52', '58'])).
% 0.36/0.57  thf('60', plain,
% 0.36/0.57      ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['57', '59'])).
% 0.36/0.57  thf('61', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i]:
% 0.36/0.57         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.36/0.57          | ~ (v1_relat_1 @ X10))),
% 0.36/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.57  thf(t46_relat_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( v1_relat_1 @ B ) =>
% 0.36/0.57           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.57             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.36/0.57  thf('62', plain,
% 0.36/0.57      (![X14 : $i, X15 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X14)
% 0.36/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) = (k1_relat_1 @ X15))
% 0.36/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X14))
% 0.36/0.57          | ~ (v1_relat_1 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.36/0.57  thf('63', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X2))
% 0.36/0.57          | ~ (v1_relat_1 @ X1)
% 0.36/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.36/0.57          | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.36/0.57              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.36/0.57          | ~ (v1_relat_1 @ X2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.57  thf('64', plain,
% 0.36/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.57        | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.36/0.57            = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 0.36/0.57        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.36/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['60', '63'])).
% 0.36/0.57  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('66', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.36/0.57      inference('split', [status(esa)], ['4'])).
% 0.36/0.57  thf('67', plain,
% 0.36/0.57      (![X18 : $i, X19 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.36/0.57          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 0.36/0.57          | ~ (v1_relat_1 @ X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.36/0.57  thf('68', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ sk_A)
% 0.36/0.57         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.57  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('70', plain,
% 0.36/0.57      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 0.36/0.57         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.36/0.57      inference('demod', [status(thm)], ['68', '69'])).
% 0.36/0.57  thf('71', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.36/0.57       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('split', [status(esa)], ['4'])).
% 0.36/0.57  thf('72', plain, (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['2', '13', '52', '71'])).
% 0.36/0.57  thf('73', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.36/0.57  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('75', plain,
% 0.36/0.57      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.36/0.57          = (sk_C))
% 0.36/0.57        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))),
% 0.36/0.57      inference('demod', [status(thm)], ['64', '65', '73', '74'])).
% 0.36/0.57  thf('76', plain,
% 0.36/0.57      ((~ (v1_relat_1 @ sk_A)
% 0.36/0.57        | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.36/0.57            = (sk_C)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['55', '75'])).
% 0.36/0.57  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('78', plain,
% 0.36/0.57      (((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.36/0.57         = (sk_C))),
% 0.36/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.36/0.57  thf('79', plain,
% 0.36/0.57      (![X3 : $i, X4 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X3)
% 0.36/0.57          | ~ (v1_relat_1 @ X4)
% 0.36/0.57          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.36/0.57      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.36/0.57  thf('80', plain,
% 0.36/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X7)
% 0.36/0.57          | ((k7_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.36/0.57              = (k5_relat_1 @ (k7_relat_1 @ X8 @ X9) @ X7))
% 0.36/0.57          | ~ (v1_relat_1 @ X8))),
% 0.36/0.57      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.36/0.57  thf(t89_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ B ) =>
% 0.36/0.57       ( r1_tarski @
% 0.36/0.57         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.36/0.57  thf('81', plain,
% 0.36/0.57      (![X16 : $i, X17 : $i]:
% 0.36/0.57         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X16 @ X17)) @ 
% 0.36/0.57           (k1_relat_1 @ X16))
% 0.36/0.57          | ~ (v1_relat_1 @ X16))),
% 0.36/0.57      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.36/0.57  thf('82', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         ((r1_tarski @ 
% 0.36/0.57           (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 0.36/0.57           (k1_relat_1 @ (k5_relat_1 @ X2 @ X0)))
% 0.36/0.57          | ~ (v1_relat_1 @ X2)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['80', '81'])).
% 0.36/0.57  thf('83', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X1)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X1)
% 0.36/0.57          | (r1_tarski @ 
% 0.36/0.57             (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 0.36/0.57             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['79', '82'])).
% 0.36/0.57  thf('84', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         ((r1_tarski @ 
% 0.36/0.57           (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 0.36/0.57           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.36/0.57          | ~ (v1_relat_1 @ X1)
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['83'])).
% 0.36/0.57  thf('85', plain,
% 0.36/0.57      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.36/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.36/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.36/0.57      inference('sup+', [status(thm)], ['78', '84'])).
% 0.36/0.57  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('88', plain,
% 0.36/0.57      ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.36/0.57  thf('89', plain, ($false), inference('demod', [status(thm)], ['54', '88'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
