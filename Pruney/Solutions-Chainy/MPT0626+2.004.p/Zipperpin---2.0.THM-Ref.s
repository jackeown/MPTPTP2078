%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ouaGbP4KtF

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 578 expanded)
%              Number of leaves         :   21 ( 165 expanded)
%              Depth                    :   20
%              Number of atoms          :  941 (8810 expanded)
%              Number of equality atoms :   13 (  62 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t21_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
            <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
                & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_funct_1])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X8 @ X9 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k10_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('25',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k10_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_D @ X7 @ X5 @ X6 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X14 )
      | ( X15
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( sk_D @ sk_C_1 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('40',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['7','22','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['6','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('46',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['7','22','40','45'])).

thf('47',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['44','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('50',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['7','22','40','49'])).

thf('51',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k10_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_D @ X7 @ X5 @ X6 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X4 ) @ X7 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ X6 @ ( k10_relat_1 @ X7 @ X5 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k10_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['7','22','40','49'])).

thf('71',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61','71'])).

thf('73',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X14 )
      | ( X15
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_D @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
    = ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['72','78'])).

thf('80',plain,(
    r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['42','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ouaGbP4KtF
% 0.13/0.37  % Computer   : n013.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:54:40 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 99 iterations in 0.070s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(t182_relat_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( v1_relat_1 @ B ) =>
% 0.22/0.55           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.22/0.55             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      (![X11 : $i, X12 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X11)
% 0.22/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.22/0.55              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 0.22/0.55          | ~ (v1_relat_1 @ X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.22/0.55  thf(t21_funct_1, conjecture,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.55           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.22/0.55             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.55               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i]:
% 0.22/0.55        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.55          ( ![C:$i]:
% 0.22/0.55            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.55              ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.22/0.55                ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.55                  ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t21_funct_1])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.22/0.55        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.22/0.55        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('split', [status(esa)], ['1'])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (((~ (r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.55         | ~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55         | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['0', '2'])).
% 0.22/0.55  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_B))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))) | 
% 0.22/0.55       ~ ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B))) | 
% 0.22/0.55       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.55      inference('split', [status(esa)], ['1'])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X11 : $i, X12 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X11)
% 0.22/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.22/0.55              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 0.22/0.55          | ~ (v1_relat_1 @ X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.22/0.55        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('split', [status(esa)], ['9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      ((((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.55         | ~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55         | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('sup+', [status(thm)], ['8', '10'])).
% 0.22/0.55  thf('12', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_B))))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.55  thf(t167_relat_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ B ) =>
% 0.22/0.55       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X8 : $i, X9 : $i]:
% 0.22/0.55         ((r1_tarski @ (k10_relat_1 @ X8 @ X9) @ (k1_relat_1 @ X8))
% 0.22/0.55          | ~ (v1_relat_1 @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.22/0.55  thf(d3_tarski, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.55          | (r2_hidden @ X0 @ X2)
% 0.22/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X0)
% 0.22/0.55          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.22/0.55          | ~ (r2_hidden @ X2 @ (k10_relat_1 @ X0 @ X1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      ((((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)) | ~ (v1_relat_1 @ sk_C_1)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.55  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.22/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.22/0.55      inference('split', [status(esa)], ['1'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) | 
% 0.22/0.55       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_B))))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.55  thf(t166_relat_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ C ) =>
% 0.22/0.55       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.22/0.55         ( ?[D:$i]:
% 0.22/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.55             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.22/0.55             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X6 @ (k10_relat_1 @ X7 @ X5))
% 0.22/0.55          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.22/0.55          | ~ (v1_relat_1 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55         | (r2_hidden @ (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 0.22/0.55            (k1_relat_1 @ sk_B))))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (((r2_hidden @ (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 0.22/0.55         (k1_relat_1 @ sk_B)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_B))))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X6 @ (k10_relat_1 @ X7 @ X5))
% 0.22/0.55          | (r2_hidden @ (k4_tarski @ X6 @ (sk_D @ X7 @ X5 @ X6)) @ X7)
% 0.22/0.55          | ~ (v1_relat_1 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      (((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55         | (r2_hidden @ 
% 0.22/0.55            (k4_tarski @ sk_A @ (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_B) @ sk_A)) @ 
% 0.22/0.55            sk_C_1)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.55  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (((r2_hidden @ 
% 0.22/0.55         (k4_tarski @ sk_A @ (sk_D @ sk_C_1 @ (k1_relat_1 @ sk_B) @ sk_A)) @ 
% 0.22/0.55         sk_C_1))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.55  thf(t8_funct_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.55           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         (~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X14)
% 0.22/0.55          | ((X15) = (k1_funct_1 @ X14 @ X13))
% 0.22/0.55          | ~ (v1_funct_1 @ X14)
% 0.22/0.55          | ~ (v1_relat_1 @ X14))),
% 0.22/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55         | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.55         | ((sk_D @ sk_C_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.55             = (k1_funct_1 @ sk_C_1 @ sk_A))))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.55  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      ((((sk_D @ sk_C_1 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.55          = (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))))),
% 0.22/0.55      inference('demod', [status(thm)], ['27', '37'])).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      ((~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['1'])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B))) | 
% 0.22/0.55       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['7', '22', '40'])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (~ (r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_B)))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['6', '41'])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.22/0.55        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.22/0.55         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['43'])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B))) | 
% 0.22/0.55       ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['43'])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['7', '22', '40', '45'])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['44', '46'])).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.22/0.55      inference('split', [status(esa)], ['9'])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) | 
% 0.22/0.55       ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))))),
% 0.22/0.55      inference('split', [status(esa)], ['9'])).
% 0.22/0.55  thf('50', plain, (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['7', '22', '40', '49'])).
% 0.22/0.55  thf('51', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.22/0.55  thf(t169_relat_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      (![X10 : $i]:
% 0.22/0.55         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 0.22/0.55          | ~ (v1_relat_1 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X6 @ (k10_relat_1 @ X7 @ X5))
% 0.22/0.55          | (r2_hidden @ (k4_tarski @ X6 @ (sk_D @ X7 @ X5 @ X6)) @ X7)
% 0.22/0.55          | ~ (v1_relat_1 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ X0)
% 0.22/0.55          | ~ (v1_relat_1 @ X0)
% 0.22/0.55          | (r2_hidden @ 
% 0.22/0.55             (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((r2_hidden @ 
% 0.22/0.55           (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.22/0.55          | ~ (v1_relat_1 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['54'])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55        | (r2_hidden @ 
% 0.22/0.55           (k4_tarski @ sk_A @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A)) @ 
% 0.22/0.55           sk_C_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['51', '55'])).
% 0.22/0.55  thf('57', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      ((r2_hidden @ 
% 0.22/0.55        (k4_tarski @ sk_A @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A)) @ 
% 0.22/0.55        sk_C_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.55          | ~ (r2_hidden @ (k4_tarski @ X6 @ X4) @ X7)
% 0.22/0.55          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X7))
% 0.22/0.55          | (r2_hidden @ X6 @ (k10_relat_1 @ X7 @ X5))
% 0.22/0.55          | ~ (v1_relat_1 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55          | (r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ X0))
% 0.22/0.55          | ~ (r2_hidden @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A) @ 
% 0.22/0.55               (k2_relat_1 @ sk_C_1))
% 0.22/0.55          | ~ (r2_hidden @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A) @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.55  thf('61', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.22/0.55      inference('split', [status(esa)], ['9'])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      (![X10 : $i]:
% 0.22/0.55         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 0.22/0.55          | ~ (v1_relat_1 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X6 @ (k10_relat_1 @ X7 @ X5))
% 0.22/0.55          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.22/0.55          | ~ (v1_relat_1 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.55  thf('65', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ X0)
% 0.22/0.55          | ~ (v1_relat_1 @ X0)
% 0.22/0.55          | (r2_hidden @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1) @ 
% 0.22/0.55             (k2_relat_1 @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((r2_hidden @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1) @ (k2_relat_1 @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['65'])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      (((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55         | (r2_hidden @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A) @ 
% 0.22/0.55            (k2_relat_1 @ sk_C_1))))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['62', '66'])).
% 0.22/0.55  thf('68', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      (((r2_hidden @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A) @ 
% 0.22/0.55         (k2_relat_1 @ sk_C_1)))
% 0.22/0.55         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.22/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.22/0.55  thf('70', plain, (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['7', '22', '40', '49'])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      ((r2_hidden @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A) @ 
% 0.22/0.55        (k2_relat_1 @ sk_C_1))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['69', '70'])).
% 0.22/0.55  thf('72', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ X0))
% 0.22/0.55          | ~ (r2_hidden @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A) @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['60', '61', '71'])).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      ((r2_hidden @ 
% 0.22/0.55        (k4_tarski @ sk_A @ (sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A)) @ 
% 0.22/0.55        sk_C_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('74', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         (~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X14)
% 0.22/0.55          | ((X15) = (k1_funct_1 @ X14 @ X13))
% 0.22/0.55          | ~ (v1_funct_1 @ X14)
% 0.22/0.55          | ~ (v1_relat_1 @ X14))),
% 0.22/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.55        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.55        | ((sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 0.22/0.55            = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.55  thf('76', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('77', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('78', plain,
% 0.22/0.55      (((sk_D @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 0.22/0.55         = (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.22/0.55  thf('79', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ X0))
% 0.22/0.55          | ~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['72', '78'])).
% 0.22/0.55  thf('80', plain,
% 0.22/0.55      ((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['47', '79'])).
% 0.22/0.55  thf('81', plain, ($false), inference('demod', [status(thm)], ['42', '80'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
