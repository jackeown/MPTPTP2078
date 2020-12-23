%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0755+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9ELT1spIzz

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  76 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  294 (1090 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t48_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B )
        & ( v5_ordinal1 @ B ) )
     => ! [C: $i] :
          ( ( v3_ordinal1 @ C )
         => ( ( v1_relat_1 @ ( k7_relat_1 @ B @ C ) )
            & ( v5_relat_1 @ ( k7_relat_1 @ B @ C ) @ A )
            & ( v1_funct_1 @ ( k7_relat_1 @ B @ C ) )
            & ( v5_ordinal1 @ ( k7_relat_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v5_relat_1 @ B @ A )
          & ( v1_funct_1 @ B )
          & ( v5_ordinal1 @ B ) )
       => ! [C: $i] :
            ( ( v3_ordinal1 @ C )
           => ( ( v1_relat_1 @ ( k7_relat_1 @ B @ C ) )
              & ( v5_relat_1 @ ( k7_relat_1 @ B @ C ) @ A )
              & ( v1_funct_1 @ ( k7_relat_1 @ B @ C ) )
              & ( v5_ordinal1 @ ( k7_relat_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_ordinal1])).

thf('0',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A )
   <= ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B )
   <= ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(fc5_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v5_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ A @ B ) @ ( k2_relat_1 @ A ) )
        & ( v5_ordinal1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_ordinal1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v3_ordinal1 @ X6 )
      | ( v5_ordinal1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_ordinal1])).

thf('14',plain,
    ( ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
   <= ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( ~ ( v3_ordinal1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v5_ordinal1 @ sk_B ) )
   <= ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,
    ( ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v5_ordinal1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','12','20','21'])).

thf('23',plain,(
    ~ ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf('24',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc22_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
      | ~ ( v5_relat_1 @ X2 @ X4 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc22_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['23','28'])).


%------------------------------------------------------------------------------
