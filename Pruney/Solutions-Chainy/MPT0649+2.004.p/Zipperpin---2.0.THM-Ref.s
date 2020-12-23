%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BXmuM2DBk0

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:17 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 265 expanded)
%              Number of leaves         :   20 (  84 expanded)
%              Depth                    :   24
%              Number of atoms          :  961 (3925 expanded)
%              Number of equality atoms :   43 ( 244 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('2',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('3',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('4',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('5',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t56_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_funct_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X19
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( k1_funct_1 @ X18 @ X17 ) ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k1_funct_1 @ X15 @ ( k1_funct_1 @ X14 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('48',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ( X19
        = ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['46','59','60','61'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('64',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('72',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('73',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('74',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('82',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','83'])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['88','89','90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BXmuM2DBk0
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:13:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 114 iterations in 0.157s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.62  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.41/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.62  thf(fc5_funct_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.41/0.62       ( ( v1_relat_1 @ ( k4_relat_1 @ A ) ) & 
% 0.41/0.62         ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (![X8 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k4_relat_1 @ X8))
% 0.41/0.62          | ~ (v2_funct_1 @ X8)
% 0.41/0.62          | ~ (v1_funct_1 @ X8)
% 0.41/0.62          | ~ (v1_relat_1 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.41/0.62  thf(dt_k4_relat_1, axiom,
% 0.41/0.62    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X8 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k4_relat_1 @ X8))
% 0.41/0.62          | ~ (v2_funct_1 @ X8)
% 0.41/0.62          | ~ (v1_funct_1 @ X8)
% 0.41/0.62          | ~ (v1_relat_1 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (![X8 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k4_relat_1 @ X8))
% 0.41/0.62          | ~ (v2_funct_1 @ X8)
% 0.41/0.62          | ~ (v1_funct_1 @ X8)
% 0.41/0.62          | ~ (v1_relat_1 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.41/0.62  thf(t56_funct_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.62       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.41/0.62         ( ( ( A ) =
% 0.41/0.62             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.41/0.62           ( ( A ) =
% 0.41/0.62             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.62          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.41/0.62            ( ( ( A ) =
% 0.41/0.62                ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.41/0.62              ( ( A ) =
% 0.41/0.62                ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t56_funct_1])).
% 0.41/0.62  thf('6', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t8_funct_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.41/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.41/0.62           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.41/0.62          | ((X19) != (k1_funct_1 @ X18 @ X17))
% 0.41/0.62          | (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.41/0.62          | ~ (v1_funct_1 @ X18)
% 0.41/0.62          | ~ (v1_relat_1 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X18)
% 0.41/0.62          | ~ (v1_funct_1 @ X18)
% 0.41/0.62          | (r2_hidden @ (k4_tarski @ X17 @ (k1_funct_1 @ X18 @ X17)) @ X18)
% 0.41/0.62          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '8'])).
% 0.41/0.62  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.41/0.62      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.41/0.62  thf(d7_relat_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( v1_relat_1 @ B ) =>
% 0.41/0.62           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.41/0.62             ( ![C:$i,D:$i]:
% 0.41/0.62               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.41/0.62                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | ((X0) != (k4_relat_1 @ X1))
% 0.41/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.41/0.62          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.41/0.62          | ~ (v1_relat_1 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X1)
% 0.41/0.62          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.41/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k4_relat_1 @ X1))
% 0.41/0.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.41/0.62          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['13', '15'])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.41/0.62          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | (r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.41/0.62           (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '17'])).
% 0.41/0.62  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      ((r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.41/0.62        (k4_relat_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.62         (~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.41/0.62          | (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.41/0.62          | ~ (v1_funct_1 @ X18)
% 0.41/0.62          | ~ (v1_relat_1 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.41/0.62           (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.41/0.62           (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '22'])).
% 0.41/0.62  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.41/0.62         (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_B)
% 0.41/0.62        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.41/0.62           (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '25'])).
% 0.41/0.62  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('29', plain, ((v2_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.41/0.62        (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.41/0.62  thf(t21_funct_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.62       ( ![C:$i]:
% 0.41/0.62         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.62           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.41/0.62             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.41/0.62               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X11)
% 0.41/0.62          | ~ (v1_funct_1 @ X11)
% 0.41/0.62          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.41/0.62          | ~ (r2_hidden @ (k1_funct_1 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.41/0.62          | (r2_hidden @ X12 @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X13)))
% 0.41/0.62          | ~ (v1_funct_1 @ X13)
% 0.41/0.62          | ~ (v1_relat_1 @ X13))),
% 0.41/0.62      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | (r2_hidden @ sk_A @ 
% 0.41/0.62           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))
% 0.41/0.62        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.62  thf('33', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | (r2_hidden @ sk_A @ 
% 0.41/0.62           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)))))),
% 0.41/0.62      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | (r2_hidden @ sk_A @ 
% 0.41/0.62           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['3', '36'])).
% 0.41/0.62  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (((r2_hidden @ sk_A @ 
% 0.41/0.62         (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_B)
% 0.41/0.62        | (r2_hidden @ sk_A @ 
% 0.41/0.62           (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '39'])).
% 0.41/0.62  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('43', plain, ((v2_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      ((r2_hidden @ sk_A @ 
% 0.41/0.62        (k1_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))))),
% 0.41/0.62      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.41/0.62  thf(t22_funct_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.62       ( ![C:$i]:
% 0.41/0.62         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.62           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.41/0.62             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.41/0.62               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X14)
% 0.41/0.62          | ~ (v1_funct_1 @ X14)
% 0.41/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X14 @ X15) @ X16)
% 0.41/0.62              = (k1_funct_1 @ X15 @ (k1_funct_1 @ X14 @ X16)))
% 0.41/0.62          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ (k5_relat_1 @ X14 @ X15)))
% 0.41/0.62          | ~ (v1_funct_1 @ X15)
% 0.41/0.62          | ~ (v1_relat_1 @ X15))),
% 0.41/0.62      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A)
% 0.41/0.62            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X8 : $i]:
% 0.41/0.62         ((v1_funct_1 @ (k4_relat_1 @ X8))
% 0.41/0.62          | ~ (v2_funct_1 @ X8)
% 0.41/0.62          | ~ (v1_funct_1 @ X8)
% 0.41/0.62          | ~ (v1_relat_1 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc5_funct_1])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      ((r2_hidden @ (k4_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.41/0.62        (k4_relat_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.62         (~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.41/0.62          | ((X19) = (k1_funct_1 @ X18 @ X17))
% 0.41/0.62          | ~ (v1_funct_1 @ X18)
% 0.41/0.62          | ~ (v1_relat_1 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ((sk_A)
% 0.41/0.62            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | ((sk_A)
% 0.41/0.62            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['48', '51'])).
% 0.41/0.62  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      ((((sk_A)
% 0.41/0.62          = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('demod', [status(thm)], ['52', '53'])).
% 0.41/0.62  thf('55', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_B)
% 0.41/0.62        | ((sk_A)
% 0.41/0.62            = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['47', '54'])).
% 0.41/0.62  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('58', plain, ((v2_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      (((sk_A)
% 0.41/0.62         = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.41/0.62  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('62', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A)
% 0.41/0.62            = (sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['46', '59', '60', '61'])).
% 0.41/0.62  thf(d9_funct_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.41/0.62  thf('63', plain,
% 0.41/0.62      (![X7 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X7)
% 0.41/0.62          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 0.41/0.62          | ~ (v1_funct_1 @ X7)
% 0.41/0.62          | ~ (v1_relat_1 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.41/0.62  thf('64', plain,
% 0.41/0.62      ((((sk_A)
% 0.41/0.62          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.41/0.62        | ((sk_A)
% 0.41/0.62            != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('65', plain,
% 0.41/0.62      ((((sk_A)
% 0.41/0.62          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((sk_A)
% 0.41/0.62                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.41/0.62                   sk_A))))),
% 0.41/0.62      inference('split', [status(esa)], ['64'])).
% 0.41/0.62  thf('66', plain,
% 0.41/0.62      (((((sk_A)
% 0.41/0.62           != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A))
% 0.41/0.62         | ~ (v1_relat_1 @ sk_B)
% 0.41/0.62         | ~ (v1_funct_1 @ sk_B)
% 0.41/0.62         | ~ (v2_funct_1 @ sk_B)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((sk_A)
% 0.41/0.62                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.41/0.62                   sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['63', '65'])).
% 0.41/0.62  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('70', plain,
% 0.41/0.62      ((((sk_A)
% 0.41/0.62          != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((sk_A)
% 0.41/0.62                = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 0.41/0.62                   sk_A))))),
% 0.41/0.62      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.41/0.62  thf('71', plain,
% 0.41/0.62      (((sk_A)
% 0.41/0.62         = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.41/0.62  thf('72', plain,
% 0.41/0.62      (![X7 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X7)
% 0.41/0.62          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 0.41/0.62          | ~ (v1_funct_1 @ X7)
% 0.41/0.62          | ~ (v1_relat_1 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      ((((sk_A)
% 0.41/0.62          != (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.41/0.62         <= (~
% 0.41/0.62             (((sk_A)
% 0.41/0.62                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.41/0.62                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.41/0.62      inference('split', [status(esa)], ['64'])).
% 0.41/0.62  thf('74', plain,
% 0.41/0.62      (((((sk_A)
% 0.41/0.62           != (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.41/0.62         | ~ (v1_relat_1 @ sk_B)
% 0.41/0.62         | ~ (v1_funct_1 @ sk_B)
% 0.41/0.62         | ~ (v2_funct_1 @ sk_B)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((sk_A)
% 0.41/0.62                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.41/0.62                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.41/0.62  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('77', plain, ((v2_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('78', plain,
% 0.41/0.62      ((((sk_A)
% 0.41/0.62          != (k1_funct_1 @ (k4_relat_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))
% 0.41/0.62         <= (~
% 0.41/0.62             (((sk_A)
% 0.41/0.62                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.41/0.62                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.41/0.62      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.41/0.62  thf('79', plain,
% 0.41/0.62      ((((sk_A) != (sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((sk_A)
% 0.41/0.62                = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.41/0.62                   (k1_funct_1 @ sk_B @ sk_A)))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['71', '78'])).
% 0.41/0.62  thf('80', plain,
% 0.41/0.62      ((((sk_A)
% 0.41/0.62          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['79'])).
% 0.41/0.62  thf('81', plain,
% 0.41/0.62      (~
% 0.41/0.62       (((sk_A)
% 0.41/0.62          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))) | 
% 0.41/0.62       ~
% 0.41/0.62       (((sk_A)
% 0.41/0.62          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.41/0.62      inference('split', [status(esa)], ['64'])).
% 0.41/0.62  thf('82', plain,
% 0.41/0.62      (~
% 0.41/0.62       (((sk_A)
% 0.41/0.62          = (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['80', '81'])).
% 0.41/0.62  thf('83', plain,
% 0.41/0.62      (((sk_A)
% 0.41/0.62         != (k1_funct_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ sk_A))),
% 0.41/0.62      inference('simpl_trail', [status(thm)], ['70', '82'])).
% 0.41/0.62  thf('84', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['62', '83'])).
% 0.41/0.62  thf('85', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '84'])).
% 0.41/0.62  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('87', plain, (~ (v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.41/0.62  thf('88', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['0', '87'])).
% 0.41/0.62  thf('89', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('90', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('91', plain, ((v2_funct_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('92', plain, ($false),
% 0.41/0.62      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
