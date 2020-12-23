%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0798+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bufx3UnDIR

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 131 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  324 (1043 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t50_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r4_wellord1 @ A @ B )
             => ( r4_wellord1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_wellord1])).

thf('2',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
          <=> ? [C: $i] :
                ( ( r3_wellord1 @ A @ B @ C )
                & ( v1_funct_1 @ C )
                & ( v1_relat_1 @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( r3_wellord1 @ X1 @ X0 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t49_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
               => ( r3_wellord1 @ B @ A @ ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r3_wellord1 @ X5 @ X4 @ X6 )
      | ( r3_wellord1 @ X4 @ X5 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t49_wellord1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( r3_wellord1 @ sk_B @ sk_A @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( v1_relat_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r3_wellord1 @ sk_B @ sk_A @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','16','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r3_wellord1 @ X1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r4_wellord1 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r4_wellord1 @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r4_wellord1 @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( r4_wellord1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','31'])).

thf('33',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('34',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('35',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('38',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37','38'])).


%------------------------------------------------------------------------------
