%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0947+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.myLe4yvJ98

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 36.83s
% Output     : Refutation 36.83s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 409 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_C_96_type,type,(
    sk_C_96: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(sk_B_82_type,type,(
    sk_B_82: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(t12_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r4_wellord1 @ ( A @ ( k1_wellord2 @ B ) ) )
                  & ( r4_wellord1 @ ( A @ ( k1_wellord2 @ C ) ) ) )
               => ( B = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ( ( ( r4_wellord1 @ ( A @ ( k1_wellord2 @ B ) ) )
                    & ( r4_wellord1 @ ( A @ ( k1_wellord2 @ C ) ) ) )
                 => ( B = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_wellord2])).

thf('0',plain,(
    r4_wellord1 @ ( sk_A_16 @ ( k1_wellord2 @ sk_C_96 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r4_wellord1 @ ( sk_A_16 @ ( k1_wellord2 @ sk_B_82 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ ( A @ B ) )
           => ( r4_wellord1 @ ( B @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X3473: $i,X3474: $i] :
      ( ~ ( v1_relat_1 @ X3473 )
      | ( r4_wellord1 @ ( X3473 @ X3474 ) )
      | ~ ( r4_wellord1 @ ( X3474 @ X3473 ) )
      | ~ ( v1_relat_1 @ X3474 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_A_16 )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B_82 @ sk_A_16 ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B_82 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('5',plain,(
    ! [X4443: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X4443 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('6',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B_82 @ sk_A_16 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t52_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ ( A @ B ) )
                  & ( r4_wellord1 @ ( B @ C ) ) )
               => ( r4_wellord1 @ ( A @ C ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X3480: $i,X3481: $i,X3482: $i] :
      ( ~ ( v1_relat_1 @ X3480 )
      | ~ ( r4_wellord1 @ ( X3481 @ X3480 ) )
      | ~ ( r4_wellord1 @ ( X3480 @ X3482 ) )
      | ( r4_wellord1 @ ( X3481 @ X3482 ) )
      | ~ ( v1_relat_1 @ X3482 )
      | ~ ( v1_relat_1 @ X3481 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B_82 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B_82 @ X0 ) )
      | ~ ( r4_wellord1 @ ( sk_A_16 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_A_16 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4443: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X4443 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('10',plain,(
    v1_relat_1 @ sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B_82 @ X0 ) )
      | ~ ( r4_wellord1 @ ( sk_A_16 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_B_82 @ ( k1_wellord2 @ sk_C_96 ) ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_C_96 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X4443: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X4443 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('14',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B_82 @ ( k1_wellord2 @ sk_C_96 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t11_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A @ ( k1_wellord2 @ B ) ) )
           => ( A = B ) ) ) ) )).

thf('15',plain,(
    ! [X4453: $i,X4454: $i] :
      ( ~ ( v3_ordinal1 @ X4453 )
      | ( X4454 = X4453 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X4454 @ ( k1_wellord2 @ X4453 ) ) )
      | ~ ( v3_ordinal1 @ X4454 ) ) ),
    inference(cnf,[status(esa)],[t11_wellord2])).

thf('16',plain,
    ( ~ ( v3_ordinal1 @ sk_B_82 )
    | ( sk_B_82 = sk_C_96 )
    | ~ ( v3_ordinal1 @ sk_C_96 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B_82 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_ordinal1 @ sk_C_96 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B_82 = sk_C_96 ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    sk_B_82 != sk_C_96 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
