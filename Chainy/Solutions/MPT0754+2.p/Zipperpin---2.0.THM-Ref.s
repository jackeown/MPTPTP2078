%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0754+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rWeHmThvrx

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 10.52s
% Output     : Refutation 10.52s
% Verified   : 
% Statistics : Number of formulae       :   48 (  75 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  221 ( 728 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_43_type,type,(
    sk_B_43: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_63_type,type,(
    sk_C_63: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t47_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ ( C @ A ) )
            & ( v1_funct_1 @ C )
            & ( v5_ordinal1 @ C ) )
         => ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ ( C @ B ) )
            & ( v1_funct_1 @ C )
            & ( v5_ordinal1 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( A @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v5_relat_1 @ ( C @ A ) )
              & ( v1_funct_1 @ C )
              & ( v5_ordinal1 @ C ) )
           => ( ( v1_relat_1 @ C )
              & ( v5_relat_1 @ ( C @ B ) )
              & ( v1_funct_1 @ C )
              & ( v5_ordinal1 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_ordinal1])).

thf('0',plain,
    ( ~ ( v1_relat_1 @ sk_C_63 )
    | ~ ( v5_relat_1 @ ( sk_C_63 @ sk_B_43 ) )
    | ~ ( v1_funct_1 @ sk_C_63 )
    | ~ ( v5_ordinal1 @ sk_C_63 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_relat_1 @ ( sk_C_63 @ sk_B_43 ) )
   <= ~ ( v5_relat_1 @ ( sk_C_63 @ sk_B_43 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C_63 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C_63 )
   <= ~ ( v1_funct_1 @ sk_C_63 ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_C_63 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v5_ordinal1 @ sk_C_63 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v5_ordinal1 @ sk_C_63 )
   <= ~ ( v5_ordinal1 @ sk_C_63 ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    v5_ordinal1 @ sk_C_63 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C_63 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_63 )
   <= ~ ( v1_relat_1 @ sk_C_63 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_63 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v5_relat_1 @ ( sk_C_63 @ sk_B_43 ) )
    | ~ ( v1_relat_1 @ sk_C_63 )
    | ~ ( v5_ordinal1 @ sk_C_63 )
    | ~ ( v1_funct_1 @ sk_C_63 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( v5_relat_1 @ ( sk_C_63 @ sk_B_43 ) ) ),
    inference('sat_resolution*',[status(thm)],['4','7','10','11'])).

thf('13',plain,(
    ~ ( v5_relat_1 @ ( sk_C_63 @ sk_B_43 ) ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,(
    v5_relat_1 @ ( sk_C_63 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_63 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_63 @ sk_A_14 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_63 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_63 @ sk_A_14 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( sk_A_14 @ sk_B_43 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('20',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( sk_A_14 @ sk_B_43 ) )
    = sk_A_14 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf('23',plain,(
    ! [X177: $i,X178: $i,X179: $i] :
      ( ( r1_tarski @ ( X177 @ X178 ) )
      | ~ ( r1_tarski @ ( X177 @ ( k3_xboole_0 @ ( X178 @ X179 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r1_tarski @ ( X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_A_14 ) )
      | ( r1_tarski @ ( X0 @ sk_B_43 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_63 @ sk_B_43 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C_63 )
    | ( v5_relat_1 @ ( sk_C_63 @ sk_B_43 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_63 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_relat_1 @ ( sk_C_63 @ sk_B_43 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['13','30'])).

%------------------------------------------------------------------------------
