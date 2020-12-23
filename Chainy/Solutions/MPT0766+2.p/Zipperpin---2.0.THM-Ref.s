%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0766+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s9RJxE48i6

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 38.53s
% Output     : Refutation 38.53s
% Verified   : 
% Statistics : Number of formulae       :   37 (  70 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  238 (1255 expanded)
%              Number of equality atoms :    2 (  24 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_55_type,type,(
    sk_B_55: $i )).

thf(sk_D_69_type,type,(
    sk_D_69: $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(t12_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ ( B @ ( k3_relat_1 @ A ) ) )
              & ? [C: $i] :
                  ( ~ ( r2_hidden @ ( k4_tarski @ ( C @ B ) @ A ) )
                  & ( r2_hidden @ ( C @ ( k3_relat_1 @ A ) ) ) )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ ( C @ ( k3_relat_1 @ A ) ) )
                    & ( r2_hidden @ ( k4_tarski @ ( B @ C ) @ A ) )
                    & ! [D: $i] :
                        ~ ( ( r2_hidden @ ( D @ ( k3_relat_1 @ A ) ) )
                          & ( r2_hidden @ ( k4_tarski @ ( B @ D ) @ A ) )
                          & ( D != B )
                          & ~ ( r2_hidden @ ( k4_tarski @ ( C @ D ) @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v2_wellord1 @ A )
         => ! [B: $i] :
              ~ ( ( r2_hidden @ ( B @ ( k3_relat_1 @ A ) ) )
                & ? [C: $i] :
                    ( ~ ( r2_hidden @ ( k4_tarski @ ( C @ B ) @ A ) )
                    & ( r2_hidden @ ( C @ ( k3_relat_1 @ A ) ) ) )
                & ! [C: $i] :
                    ~ ( ( r2_hidden @ ( C @ ( k3_relat_1 @ A ) ) )
                      & ( r2_hidden @ ( k4_tarski @ ( B @ C ) @ A ) )
                      & ! [D: $i] :
                          ~ ( ( r2_hidden @ ( D @ ( k3_relat_1 @ A ) ) )
                            & ( r2_hidden @ ( k4_tarski @ ( B @ D ) @ A ) )
                            & ( D != B )
                            & ~ ( r2_hidden @ ( k4_tarski @ ( C @ D ) @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_wellord1])).

thf('0',plain,(
    r2_hidden @ ( sk_B_55 @ ( k3_relat_1 @ sk_A_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ ( B @ ( k3_relat_1 @ A ) ) )
           => ( r2_hidden @ ( k4_tarski @ ( B @ B ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X3293: $i,X3294: $i] :
      ( ~ ( v1_relat_2 @ X3293 )
      | ( r2_hidden @ ( k4_tarski @ ( X3294 @ X3294 ) @ X3293 ) )
      | ~ ( r2_hidden @ ( X3294 @ ( k3_relat_1 @ X3293 ) ) )
      | ~ ( v1_relat_1 @ X3293 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_55 @ sk_B_55 ) @ sk_A_14 ) )
    | ~ ( v1_relat_2 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X3281: $i] :
      ( ~ ( v2_wellord1 @ X3281 )
      | ( v1_relat_2 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('6',plain,
    ( ( v1_relat_2 @ sk_A_14 )
    | ~ ( v2_wellord1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_wellord1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_2 @ sk_A_14 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B_55 @ sk_B_55 ) @ sk_A_14 ) ),
    inference(demod,[status(thm)],['2','3','8'])).

thf('10',plain,(
    ! [X3310: $i] :
      ( ~ ( r2_hidden @ ( X3310 @ ( k3_relat_1 @ sk_A_14 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B_55 @ X3310 ) @ sk_A_14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X3310 @ ( sk_D_69 @ X3310 ) ) @ sk_A_14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_B_55 @ ( sk_D_69 @ sk_B_55 ) ) @ sk_A_14 ) )
    | ~ ( r2_hidden @ ( sk_B_55 @ ( k3_relat_1 @ sk_A_14 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_B_55 @ ( k3_relat_1 @ sk_A_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( sk_B_55 @ ( sk_D_69 @ sk_B_55 ) ) @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B_55 @ sk_B_55 ) @ sk_A_14 ) ),
    inference(demod,[status(thm)],['2','3','8'])).

thf('15',plain,(
    ! [X3310: $i] :
      ( ~ ( r2_hidden @ ( X3310 @ ( k3_relat_1 @ sk_A_14 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B_55 @ X3310 ) @ sk_A_14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_55 @ ( sk_D_69 @ X3310 ) ) @ sk_A_14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B_55 @ ( sk_D_69 @ sk_B_55 ) ) @ sk_A_14 ) )
    | ~ ( r2_hidden @ ( sk_B_55 @ ( k3_relat_1 @ sk_A_14 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_B_55 @ ( k3_relat_1 @ sk_A_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B_55 @ ( sk_D_69 @ sk_B_55 ) ) @ sk_A_14 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['13','18'])).

%------------------------------------------------------------------------------
