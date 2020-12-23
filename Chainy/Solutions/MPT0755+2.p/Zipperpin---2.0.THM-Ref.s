%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0755+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OLfvYLxuk7

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 23.81s
% Output     : Refutation 23.81s
% Verified   : 
% Statistics : Number of formulae       :   46 (  76 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  289 (1085 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_C_63_type,type,(
    sk_C_63: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(sk_B_43_type,type,(
    sk_B_43: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(fc5_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v5_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ ( A @ B ) ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ ( A @ B ) @ ( k2_relat_1 @ A ) ) )
        & ( v5_ordinal1 @ ( k7_relat_1 @ ( A @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X3094: $i,X3095: $i] :
      ( ~ ( v5_ordinal1 @ X3094 )
      | ~ ( v1_funct_1 @ X3094 )
      | ~ ( v1_relat_1 @ X3094 )
      | ~ ( v3_ordinal1 @ X3095 )
      | ( v5_ordinal1 @ ( k7_relat_1 @ ( X3094 @ X3095 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc5_ordinal1])).

thf(t48_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ ( B @ A ) )
        & ( v1_funct_1 @ B )
        & ( v5_ordinal1 @ B ) )
     => ! [C: $i] :
          ( ( v3_ordinal1 @ C )
         => ( ( v1_relat_1 @ ( k7_relat_1 @ ( B @ C ) ) )
            & ( v5_relat_1 @ ( k7_relat_1 @ ( B @ C ) @ A ) )
            & ( v1_funct_1 @ ( k7_relat_1 @ ( B @ C ) ) )
            & ( v5_ordinal1 @ ( k7_relat_1 @ ( B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v5_relat_1 @ ( B @ A ) )
          & ( v1_funct_1 @ B )
          & ( v5_ordinal1 @ B ) )
       => ! [C: $i] :
            ( ( v3_ordinal1 @ C )
           => ( ( v1_relat_1 @ ( k7_relat_1 @ ( B @ C ) ) )
              & ( v5_relat_1 @ ( k7_relat_1 @ ( B @ C ) @ A ) )
              & ( v1_funct_1 @ ( k7_relat_1 @ ( B @ C ) ) )
              & ( v5_ordinal1 @ ( k7_relat_1 @ ( B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_ordinal1])).

thf('1',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) )
    | ~ ( v5_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) @ sk_A_14 ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) )
    | ~ ( v5_ordinal1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v5_ordinal1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) )
   <= ~ ( v5_ordinal1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ ( A @ B ) ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ ( A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X2699: $i,X2700: $i] :
      ( ~ ( v1_funct_1 @ X2699 )
      | ~ ( v1_relat_1 @ X2699 )
      | ( v1_funct_1 @ ( k7_relat_1 @ ( X2699 @ X2700 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) )
   <= ~ ( v1_funct_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('5',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_43 )
      | ~ ( v1_funct_1 @ sk_B_43 ) )
   <= ~ ( v1_funct_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B_43 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_B_43 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ ( A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X2136: $i,X2137: $i] :
      ( ~ ( v1_relat_1 @ X2136 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( X2136 @ X2137 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) )
   <= ~ ( v1_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B_43 )
   <= ~ ( v1_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B_43 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    v5_relat_1 @ ( sk_B_43 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc22_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ ( C @ B ) ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ ( C @ A ) ) )
        & ( v5_relat_1 @ ( k7_relat_1 @ ( C @ A ) @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3089: $i,X3090: $i,X3091: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ ( X3089 @ X3090 ) @ X3091 ) )
      | ~ ( v5_relat_1 @ ( X3089 @ X3091 ) )
      | ~ ( v1_relat_1 @ X3089 ) ) ),
    inference(cnf,[status(esa)],[fc22_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B_43 )
      | ( v5_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ X0 ) @ sk_A_14 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B_43 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ X0 ) @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v5_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) @ sk_A_14 ) )
   <= ~ ( v5_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) @ sk_A_14 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('20',plain,(
    v5_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v5_ordinal1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) )
    | ~ ( v5_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) @ sk_A_14 ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('22',plain,(
    ~ ( v5_ordinal1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['8','13','20','21'])).

thf('23',plain,(
    ~ ( v5_ordinal1 @ ( k7_relat_1 @ ( sk_B_43 @ sk_C_63 ) ) ) ),
    inference(simpl_trail,[status(thm)],['2','22'])).

thf('24',plain,
    ( ~ ( v3_ordinal1 @ sk_C_63 )
    | ~ ( v1_relat_1 @ sk_B_43 )
    | ~ ( v1_funct_1 @ sk_B_43 )
    | ~ ( v5_ordinal1 @ sk_B_43 ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_C_63 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B_43 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B_43 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v5_ordinal1 @ sk_B_43 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

%------------------------------------------------------------------------------
