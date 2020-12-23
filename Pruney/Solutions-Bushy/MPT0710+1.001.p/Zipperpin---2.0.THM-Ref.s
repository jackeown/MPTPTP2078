%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0710+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hT6dmiULhz

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 664 expanded)
%              Number of leaves         :   20 ( 192 expanded)
%              Depth                    :   41
%              Number of atoms          : 1864 (13001 expanded)
%              Number of equality atoms :  126 ( 870 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(t165_funct_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                        = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t165_funct_1])).

thf('9',plain,(
    r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('16',plain,(
    r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) )
       != ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ( sk_C_1
       != ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ( sk_C_1
       != ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( sk_C_1
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_1
       != ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C_1
       != ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ X0 @ X1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','35'])).

thf('37',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
      = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
      = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
      = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D )
     != ( k1_funct_1 @ sk_B @ sk_D ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
     != ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C_1 )
     != ( k7_relat_1 @ sk_B @ sk_C_1 ) )
   <= ( ( k7_relat_1 @ sk_A @ sk_C_1 )
     != ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C_1 )
     != ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_A @ sk_D )
     != ( k1_funct_1 @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['41'])).

thf('44',plain,
    ( ( r2_hidden @ sk_D @ sk_C_1 )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
     != ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ sk_D @ sk_C_1 )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
     != ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_D @ sk_C_1 )
   <= ( r2_hidden @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['44'])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X8 @ X7 ) @ X6 )
        = ( k1_funct_1 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_C_1 ) @ sk_D )
          = ( k1_funct_1 @ X0 @ sk_D ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r2_hidden @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ X13 @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_A @ X13 )
        = ( k1_funct_1 @ sk_B @ X13 ) )
      | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C_1 )
      = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
   <= ( ( k7_relat_1 @ sk_A @ sk_C_1 )
      = ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_C_1 ) @ sk_D )
          = ( k1_funct_1 @ X0 @ sk_D ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r2_hidden @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('52',plain,
    ( ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_D )
        = ( k1_funct_1 @ sk_B @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
      & ( r2_hidden @ sk_D @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_D )
      = ( k1_funct_1 @ sk_B @ sk_D ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
      & ( r2_hidden @ sk_D @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( ( ( k1_funct_1 @ sk_A @ sk_D )
        = ( k1_funct_1 @ sk_B @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
      & ( r2_hidden @ sk_D @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D )
      = ( k1_funct_1 @ sk_B @ sk_D ) )
   <= ( ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
      & ( r2_hidden @ sk_D @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D )
     != ( k1_funct_1 @ sk_B @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_A @ sk_D )
     != ( k1_funct_1 @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['41'])).

thf('61',plain,
    ( ( ( k1_funct_1 @ sk_A @ sk_D )
     != ( k1_funct_1 @ sk_A @ sk_D ) )
   <= ( ( ( k1_funct_1 @ sk_A @ sk_D )
       != ( k1_funct_1 @ sk_B @ sk_D ) )
      & ( ( k7_relat_1 @ sk_A @ sk_C_1 )
        = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
      & ( r2_hidden @ sk_D @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k7_relat_1 @ sk_A @ sk_C_1 )
     != ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D @ sk_C_1 )
    | ( ( k1_funct_1 @ sk_A @ sk_D )
      = ( k1_funct_1 @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['43','45','62'])).

thf('64',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['42','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X8 @ X7 ) @ X6 )
        = ( k1_funct_1 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_C_1 ) @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_C_1 ) @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X12 = X11 )
      | ( ( k1_funct_1 @ X12 @ ( sk_C @ X11 @ X12 ) )
       != ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ X12 ) ) )
      | ( ( k1_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('83',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
     != ( k1_funct_1 @ sk_B @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
      = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r2_hidden @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('85',plain,
    ( ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_C_1 )
        | ( ( k1_funct_1 @ sk_A @ X13 )
          = ( k1_funct_1 @ sk_B @ X13 ) ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_C_1 )
        | ( ( k1_funct_1 @ sk_A @ X13 )
          = ( k1_funct_1 @ sk_B @ X13 ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('86',plain,
    ( ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_C_1 )
        | ( ( k1_funct_1 @ sk_A @ X13 )
          = ( k1_funct_1 @ sk_B @ X13 ) ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
      = ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['49'])).

thf('87',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ X13 @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_A @ X13 )
        = ( k1_funct_1 @ sk_B @ X13 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['43','45','62','86'])).

thf('88',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ X13 @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_A @ X13 )
        = ( k1_funct_1 @ sk_B @ X13 ) ) ) ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('89',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['84','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ( ( k7_relat_1 @ sk_A @ sk_C_1 )
      = ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['83','89','90','91'])).

thf('93',plain,(
    ( k7_relat_1 @ sk_A @ sk_C_1 )
 != ( k7_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['42','63'])).

thf('94',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
     != ( k1_funct_1 @ sk_A @ ( sk_C @ ( k7_relat_1 @ sk_B @ sk_C_1 ) @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
 != ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
     != ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('118',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('119',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
 != sk_C_1 ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_C_1 )
     != sk_C_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('123',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('124',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    $false ),
    inference(simplify,[status(thm)],['125'])).


%------------------------------------------------------------------------------
