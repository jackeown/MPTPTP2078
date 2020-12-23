%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Iz25HrLW70

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:19 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 243 expanded)
%              Number of leaves         :   23 (  77 expanded)
%              Depth                    :   19
%              Number of atoms          :  883 (3407 expanded)
%              Number of equality atoms :   56 ( 226 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ( X10
       != ( k2_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X11 @ X9 ) @ X11 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( X14
       != ( k4_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X16 ) @ X15 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_3 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_3 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k1_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k1_funct_1 @ X22 @ ( k1_funct_1 @ X23 @ X24 ) ) )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('31',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ( X27
        = ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_3 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('45',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('46',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_3 @ sk_A @ sk_B ) ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ( X27
        = ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( sk_D_3 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( sk_D_3 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( sk_D_3 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( sk_D_3 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_D_3 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','56'])).

thf('58',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('59',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('60',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('68',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['37','68'])).

thf('70',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','69'])).

thf('71',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','56'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    $false ),
    inference(simplify,[status(thm)],['74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Iz25HrLW70
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 228 iterations in 0.145s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.39/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.39/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.39/0.59  thf(d9_funct_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.59       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X20 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X20)
% 0.39/0.59          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.39/0.59          | ~ (v1_funct_1 @ X20)
% 0.39/0.59          | ~ (v1_relat_1 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.39/0.59  thf(dt_k2_funct_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.59       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.39/0.59         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X21 : $i]:
% 0.39/0.59         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 0.39/0.59          | ~ (v1_funct_1 @ X21)
% 0.39/0.59          | ~ (v1_relat_1 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.59  thf(dt_k4_relat_1, axiom,
% 0.39/0.59    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X19 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X19)) | ~ (v1_relat_1 @ X19))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.39/0.59  thf(t57_funct_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.39/0.59         ( ( ( A ) =
% 0.39/0.59             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.39/0.59           ( ( A ) =
% 0.39/0.59             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i]:
% 0.39/0.59        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.39/0.59            ( ( ( A ) =
% 0.39/0.59                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.39/0.59              ( ( A ) =
% 0.39/0.59                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.39/0.59  thf('5', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d5_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.39/0.59       ( ![C:$i]:
% 0.39/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X11 @ X10)
% 0.39/0.59          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X11 @ X9) @ X11) @ X9)
% 0.39/0.59          | ((X10) != (k2_relat_1 @ X9)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X9 : $i, X11 : $i]:
% 0.39/0.59         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X11 @ X9) @ X11) @ X9)
% 0.39/0.59          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X9)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.39/0.59      inference('sup-', [status(thm)], ['5', '7'])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X19 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X19)) | ~ (v1_relat_1 @ X19))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.39/0.59  thf(d7_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( v1_relat_1 @ B ) =>
% 0.39/0.59           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.39/0.59             ( ![C:$i,D:$i]:
% 0.39/0.59               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.39/0.59                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X14)
% 0.39/0.59          | ((X14) != (k4_relat_1 @ X15))
% 0.39/0.59          | (r2_hidden @ (k4_tarski @ X16 @ X17) @ X14)
% 0.39/0.59          | ~ (r2_hidden @ (k4_tarski @ X17 @ X16) @ X15)
% 0.39/0.59          | ~ (v1_relat_1 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X15)
% 0.39/0.59          | ~ (r2_hidden @ (k4_tarski @ X17 @ X16) @ X15)
% 0.39/0.59          | (r2_hidden @ (k4_tarski @ X16 @ X17) @ (k4_relat_1 @ X15))
% 0.39/0.59          | ~ (v1_relat_1 @ (k4_relat_1 @ X15)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.39/0.59          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['9', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.39/0.59          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.59        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_D_3 @ sk_A @ sk_B)) @ 
% 0.39/0.59           (k4_relat_1 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '13'])).
% 0.39/0.59  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_3 @ sk_A @ sk_B)) @ 
% 0.39/0.59        (k4_relat_1 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.59  thf(d4_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.39/0.59       ( ![C:$i]:
% 0.39/0.59         ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.59           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.39/0.59          | (r2_hidden @ X0 @ X3)
% 0.39/0.59          | ((X3) != (k1_relat_1 @ X2)))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.39/0.59          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.39/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.59  thf('19', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '18'])).
% 0.39/0.59  thf(t23_funct_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59       ( ![C:$i]:
% 0.39/0.59         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.59           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.59             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.39/0.59               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X22)
% 0.39/0.59          | ~ (v1_funct_1 @ X22)
% 0.39/0.59          | ((k1_funct_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 0.39/0.59              = (k1_funct_1 @ X22 @ (k1_funct_1 @ X23 @ X24)))
% 0.39/0.59          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X23))
% 0.39/0.59          | ~ (v1_funct_1 @ X23)
% 0.39/0.59          | ~ (v1_relat_1 @ X23))),
% 0.39/0.59      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.39/0.59          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.39/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.39/0.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ sk_B)
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.39/0.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.59          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['4', '21'])).
% 0.39/0.59  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.39/0.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.59          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.39/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ sk_B)
% 0.39/0.59          | ~ (v1_funct_1 @ sk_B)
% 0.39/0.59          | ~ (v2_funct_1 @ sk_B)
% 0.39/0.59          | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.39/0.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['3', '24'])).
% 0.39/0.59  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('28', plain, ((v2_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.39/0.59            = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X20 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X20)
% 0.39/0.59          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.39/0.59          | ~ (v1_funct_1 @ X20)
% 0.39/0.59          | ~ (v1_relat_1 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      ((((sk_A)
% 0.39/0.59          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.39/0.59        | ((sk_A)
% 0.39/0.59            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      ((((sk_A)
% 0.39/0.59          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.39/0.59         <= (~
% 0.39/0.59             (((sk_A)
% 0.39/0.59                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.39/0.59                   sk_A))))),
% 0.39/0.59      inference('split', [status(esa)], ['31'])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (((((sk_A)
% 0.39/0.59           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.39/0.59         | ~ (v1_relat_1 @ sk_B)
% 0.39/0.59         | ~ (v1_funct_1 @ sk_B)
% 0.39/0.59         | ~ (v2_funct_1 @ sk_B)))
% 0.39/0.59         <= (~
% 0.39/0.59             (((sk_A)
% 0.39/0.59                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.39/0.59                   sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['30', '32'])).
% 0.39/0.59  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('36', plain, ((v2_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      ((((sk_A)
% 0.39/0.59          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.39/0.59         <= (~
% 0.39/0.59             (((sk_A)
% 0.39/0.59                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.39/0.59                   sk_A))))),
% 0.39/0.59      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.39/0.59      inference('sup-', [status(thm)], ['5', '7'])).
% 0.39/0.59  thf(t8_funct_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.59       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.39/0.59         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.39/0.59           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.59         (~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.39/0.59          | ((X27) = (k1_funct_1 @ X26 @ X25))
% 0.39/0.59          | ~ (v1_funct_1 @ X26)
% 0.39/0.59          | ~ (v1_relat_1 @ X26))),
% 0.39/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.59        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.59  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('43', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_3 @ sk_A @ sk_B)))),
% 0.39/0.59      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      (![X19 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X19)) | ~ (v1_relat_1 @ X19))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_3 @ sk_A @ sk_B)) @ 
% 0.39/0.59        (k4_relat_1 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.59         (~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.39/0.59          | ((X27) = (k1_funct_1 @ X26 @ X25))
% 0.39/0.59          | ~ (v1_funct_1 @ X26)
% 0.39/0.59          | ~ (v1_relat_1 @ X26))),
% 0.39/0.59      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.39/0.59        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.39/0.59        | ((sk_D_3 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.59        | ((sk_D_3 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.39/0.59        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['45', '48'])).
% 0.39/0.59  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      ((((sk_D_3 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.39/0.59        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.39/0.59      inference('demod', [status(thm)], ['49', '50'])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_B)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_B)
% 0.39/0.59        | ((sk_D_3 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['44', '51'])).
% 0.39/0.59  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('55', plain, ((v2_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('56', plain,
% 0.39/0.59      (((sk_D_3 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      (((sk_A)
% 0.39/0.59         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['43', '56'])).
% 0.39/0.59  thf('58', plain,
% 0.39/0.59      (![X20 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X20)
% 0.39/0.59          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.39/0.59          | ~ (v1_funct_1 @ X20)
% 0.39/0.59          | ~ (v1_relat_1 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.39/0.59  thf('59', plain,
% 0.39/0.59      ((((sk_A)
% 0.39/0.59          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.39/0.59         <= (~
% 0.39/0.59             (((sk_A)
% 0.39/0.59                = (k1_funct_1 @ sk_B @ 
% 0.39/0.59                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.39/0.59      inference('split', [status(esa)], ['31'])).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      (((((sk_A)
% 0.39/0.59           != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.59         | ~ (v1_relat_1 @ sk_B)
% 0.39/0.59         | ~ (v1_funct_1 @ sk_B)
% 0.39/0.59         | ~ (v2_funct_1 @ sk_B)))
% 0.39/0.59         <= (~
% 0.39/0.59             (((sk_A)
% 0.39/0.59                = (k1_funct_1 @ sk_B @ 
% 0.39/0.59                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.59  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('63', plain, ((v2_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('64', plain,
% 0.39/0.59      ((((sk_A)
% 0.39/0.59          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))))
% 0.39/0.59         <= (~
% 0.39/0.59             (((sk_A)
% 0.39/0.59                = (k1_funct_1 @ sk_B @ 
% 0.39/0.59                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.39/0.59  thf('65', plain,
% 0.39/0.59      ((((sk_A) != (sk_A)))
% 0.39/0.59         <= (~
% 0.39/0.59             (((sk_A)
% 0.39/0.59                = (k1_funct_1 @ sk_B @ 
% 0.39/0.59                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['57', '64'])).
% 0.39/0.59  thf('66', plain,
% 0.39/0.59      ((((sk_A)
% 0.39/0.59          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['65'])).
% 0.39/0.59  thf('67', plain,
% 0.39/0.59      (~
% 0.39/0.59       (((sk_A)
% 0.39/0.59          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.39/0.59       ~
% 0.39/0.59       (((sk_A)
% 0.39/0.59          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.39/0.59      inference('split', [status(esa)], ['31'])).
% 0.39/0.59  thf('68', plain,
% 0.39/0.59      (~
% 0.39/0.59       (((sk_A)
% 0.39/0.59          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.39/0.59  thf('69', plain,
% 0.39/0.59      (((sk_A)
% 0.39/0.59         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['37', '68'])).
% 0.39/0.59  thf('70', plain,
% 0.39/0.59      ((((sk_A)
% 0.39/0.59          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.39/0.59        | ~ (v1_relat_1 @ sk_B)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '69'])).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (((sk_A)
% 0.39/0.59         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['43', '56'])).
% 0.39/0.59  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('74', plain, (((sk_A) != (sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.39/0.59  thf('75', plain, ($false), inference('simplify', [status(thm)], ['74'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
