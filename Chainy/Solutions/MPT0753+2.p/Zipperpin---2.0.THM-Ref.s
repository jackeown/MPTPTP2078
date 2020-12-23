%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0753+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AanKvLHtzh

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 491 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( X0 @ X0 ) )
      | ( r1_tarski @ ( X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t46_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) )
       => ( ( v1_relat_1 @ A )
          & ( v5_relat_1 @ ( A @ ( k2_relat_1 @ A ) ) )
          & ( v1_funct_1 @ A )
          & ( v5_ordinal1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) )
         => ( ( v1_relat_1 @ A )
            & ( v5_relat_1 @ ( A @ ( k2_relat_1 @ A ) ) )
            & ( v1_funct_1 @ A )
            & ( v5_ordinal1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_ordinal1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v5_relat_1 @ ( sk_A_14 @ ( k2_relat_1 @ sk_A_14 ) ) )
    | ~ ( v1_funct_1 @ sk_A_14 )
    | ~ ( v5_ordinal1 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v5_relat_1 @ ( sk_A_14 @ ( k2_relat_1 @ sk_A_14 ) ) )
   <= ~ ( v5_relat_1 @ ( sk_A_14 @ ( k2_relat_1 @ sk_A_14 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    v1_funct_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_A_14 )
   <= ~ ( v1_funct_1 @ sk_A_14 ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,(
    v1_funct_1 @ sk_A_14 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
   <= ~ ( v1_relat_1 @ sk_A_14 ) ),
    inference(split,[status(esa)],['6'])).

thf('13',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ ( k1_relat_1 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ A )
    <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X3083: $i] :
      ( ( v5_ordinal1 @ X3083 )
      | ~ ( v3_ordinal1 @ ( k1_relat_1 @ X3083 ) ) ) ),
    inference(cnf,[status(esa)],[d7_ordinal1])).

thf('16',plain,(
    v5_ordinal1 @ sk_A_14 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v5_ordinal1 @ sk_A_14 )
   <= ~ ( v5_ordinal1 @ sk_A_14 ) ),
    inference(split,[status(esa)],['6'])).

thf('18',plain,(
    v5_ordinal1 @ sk_A_14 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v5_relat_1 @ ( sk_A_14 @ ( k2_relat_1 @ sk_A_14 ) ) )
    | ~ ( v5_ordinal1 @ sk_A_14 )
    | ~ ( v1_relat_1 @ sk_A_14 )
    | ~ ( v1_funct_1 @ sk_A_14 ) ),
    inference(split,[status(esa)],['6'])).

thf('20',plain,(
    ~ ( v5_relat_1 @ ( sk_A_14 @ ( k2_relat_1 @ sk_A_14 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','13','18','19'])).

thf('21',plain,(
    ~ ( v5_relat_1 @ ( sk_A_14 @ ( k2_relat_1 @ sk_A_14 ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','20'])).

thf('22',plain,(
    ~ ( v1_relat_1 @ sk_A_14 ) ),
    inference('sup-',[status(thm)],['5','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
