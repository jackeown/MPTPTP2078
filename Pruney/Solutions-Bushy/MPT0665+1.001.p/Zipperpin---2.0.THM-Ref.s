%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0665+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XQTiBnNc76

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:17 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  413 ( 755 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t73_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ A @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X19 @ X18 ) @ X17 )
        = ( k1_funct_1 @ X19 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

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

thf('13',plain,(
    ! [X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X7 ) )
      | ( X11
       != ( k1_funct_1 @ X7 @ X12 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('14',plain,(
    ! [X7: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X12 ) @ ( k2_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).


%------------------------------------------------------------------------------
