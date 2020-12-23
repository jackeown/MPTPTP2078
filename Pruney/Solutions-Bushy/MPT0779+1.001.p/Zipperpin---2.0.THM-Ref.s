%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0779+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gjK2JZvvxV

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:29 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   14
%              Number of atoms          :  361 ( 464 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_wellord1 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_wellord1 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_wellord1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_wellord1 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X0 )
        = ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X1 @ X0 ) @ X0 )
        = ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t28_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A )
        = ( k2_wellord1 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A )
          = ( k2_wellord1 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_wellord1])).

thf('19',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_B @ sk_A ) @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_wellord1 @ sk_B @ sk_A )
     != ( k2_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).


%------------------------------------------------------------------------------
