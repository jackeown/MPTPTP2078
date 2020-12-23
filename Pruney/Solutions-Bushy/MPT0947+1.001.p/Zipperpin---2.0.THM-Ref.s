%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0947+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k0NYmujisN

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 409 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t12_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r4_wellord1 @ A @ ( k1_wellord2 @ B ) )
                  & ( r4_wellord1 @ A @ ( k1_wellord2 @ C ) ) )
               => ( B = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ( ( ( r4_wellord1 @ A @ ( k1_wellord2 @ B ) )
                    & ( r4_wellord1 @ A @ ( k1_wellord2 @ C ) ) )
                 => ( B = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_wellord2])).

thf('0',plain,(
    r4_wellord1 @ sk_A @ ( k1_wellord2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r4_wellord1 @ sk_A @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r4_wellord1 @ X3 @ X4 )
      | ~ ( r4_wellord1 @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('6',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t52_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ A @ B )
                  & ( r4_wellord1 @ B @ C ) )
               => ( r4_wellord1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r4_wellord1 @ X6 @ X5 )
      | ~ ( r4_wellord1 @ X5 @ X7 )
      | ( r4_wellord1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('14',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t11_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X2 = X1 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X2 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t11_wellord2])).

thf('16',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B = sk_C )
    | ~ ( v3_ordinal1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B = sk_C ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).


%------------------------------------------------------------------------------
