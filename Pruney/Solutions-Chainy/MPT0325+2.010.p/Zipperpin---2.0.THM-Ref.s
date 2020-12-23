%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.siDfBXgrEa

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:41 EST 2020

% Result     : Theorem 17.50s
% Output     : Refutation 17.50s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 507 expanded)
%              Number of leaves         :   25 ( 160 expanded)
%              Depth                    :   21
%              Number of atoms          : 1745 (4933 expanded)
%              Number of equality atoms :  108 ( 318 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X17: $i] :
      ( r1_tarski @ X17 @ X17 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X26 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X1 ) @ X4 ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ( ( k3_xboole_0 @ X3 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('28',plain,(
    ! [X16: $i,X18: $i] :
      ( ( X16 = X18 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('44',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('56',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) @ sk_D_1 ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) @ sk_D_1 ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_2 ) @ sk_D_1 ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','62'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('64',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_zfmisc_1 @ X24 @ X25 )
        = k1_xboole_0 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    ! [X25: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,
    ( ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('68',plain,(
    ! [X25: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('70',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('71',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('73',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('74',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['63','65','66','67','68','75'])).

thf('77',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('78',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('85',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['76','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
        = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
        = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['92','95','96'])).

thf('98',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['6','97'])).

thf('99',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('108',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('109',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X27 @ X26 ) @ ( k2_zfmisc_1 @ X28 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X3 @ X1 ) )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('114',plain,
    ( ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('117',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('126',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X29 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['124','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['123','136'])).

thf('138',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('139',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ k1_xboole_0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('147',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ k1_xboole_0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ k1_xboole_0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('151',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','151'])).

thf('153',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_zfmisc_1 @ X24 @ X25 )
        = k1_xboole_0 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('154',plain,(
    ! [X24: $i] :
      ( ( k2_zfmisc_1 @ X24 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('156',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['152','154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('158',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['103','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.siDfBXgrEa
% 0.12/0.36  % Computer   : n003.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 15:58:12 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 17.50/17.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 17.50/17.69  % Solved by: fo/fo7.sh
% 17.50/17.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.50/17.69  % done 12578 iterations in 17.206s
% 17.50/17.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 17.50/17.69  % SZS output start Refutation
% 17.50/17.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.50/17.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 17.50/17.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 17.50/17.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.50/17.69  thf(sk_A_type, type, sk_A: $i).
% 17.50/17.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 17.50/17.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.50/17.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.50/17.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 17.50/17.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 17.50/17.69  thf(sk_B_type, type, sk_B: $i).
% 17.50/17.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.50/17.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 17.50/17.69  thf(t138_zfmisc_1, conjecture,
% 17.50/17.69    (![A:$i,B:$i,C:$i,D:$i]:
% 17.50/17.69     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 17.50/17.69       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 17.50/17.69         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 17.50/17.69  thf(zf_stmt_0, negated_conjecture,
% 17.50/17.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 17.50/17.69        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 17.50/17.69          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 17.50/17.69            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 17.50/17.69    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 17.50/17.69  thf('0', plain,
% 17.50/17.69      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 17.50/17.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.50/17.69  thf('1', plain,
% 17.50/17.69      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 17.50/17.69      inference('split', [status(esa)], ['0'])).
% 17.50/17.69  thf('2', plain,
% 17.50/17.69      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 17.50/17.69        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 17.50/17.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.50/17.69  thf(t28_xboole_1, axiom,
% 17.50/17.69    (![A:$i,B:$i]:
% 17.50/17.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 17.50/17.69  thf('3', plain,
% 17.50/17.69      (![X19 : $i, X20 : $i]:
% 17.50/17.69         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 17.50/17.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.50/17.69  thf('4', plain,
% 17.50/17.69      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.50/17.69      inference('sup-', [status(thm)], ['2', '3'])).
% 17.50/17.69  thf(commutativity_k3_xboole_0, axiom,
% 17.50/17.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 17.50/17.69  thf('5', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.50/17.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.50/17.69  thf('6', plain,
% 17.50/17.69      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.50/17.69      inference('demod', [status(thm)], ['4', '5'])).
% 17.50/17.69  thf(d10_xboole_0, axiom,
% 17.50/17.69    (![A:$i,B:$i]:
% 17.50/17.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 17.50/17.69  thf('7', plain,
% 17.50/17.69      (![X16 : $i, X17 : $i]: ((r1_tarski @ X16 @ X17) | ((X16) != (X17)))),
% 17.50/17.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.50/17.69  thf('8', plain, (![X17 : $i]: (r1_tarski @ X17 @ X17)),
% 17.50/17.69      inference('simplify', [status(thm)], ['7'])).
% 17.50/17.69  thf('9', plain,
% 17.50/17.69      (![X19 : $i, X20 : $i]:
% 17.50/17.69         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 17.50/17.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.50/17.69  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['8', '9'])).
% 17.50/17.69  thf(t123_zfmisc_1, axiom,
% 17.50/17.69    (![A:$i,B:$i,C:$i,D:$i]:
% 17.50/17.69     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 17.50/17.69       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 17.50/17.69  thf('11', plain,
% 17.50/17.69      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 17.50/17.69              (k2_zfmisc_1 @ X31 @ X32)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 17.50/17.69  thf('12', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['10', '11'])).
% 17.50/17.69  thf(d3_tarski, axiom,
% 17.50/17.69    (![A:$i,B:$i]:
% 17.50/17.69     ( ( r1_tarski @ A @ B ) <=>
% 17.50/17.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 17.50/17.69  thf('13', plain,
% 17.50/17.69      (![X3 : $i, X5 : $i]:
% 17.50/17.69         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 17.50/17.69      inference('cnf', [status(esa)], [d3_tarski])).
% 17.50/17.69  thf(d4_xboole_0, axiom,
% 17.50/17.69    (![A:$i,B:$i,C:$i]:
% 17.50/17.69     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 17.50/17.69       ( ![D:$i]:
% 17.50/17.69         ( ( r2_hidden @ D @ C ) <=>
% 17.50/17.69           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 17.50/17.69  thf('14', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X10 @ X9)
% 17.50/17.69          | (r2_hidden @ X10 @ X8)
% 17.50/17.69          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 17.50/17.69      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.50/17.69  thf('15', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X10 : $i]:
% 17.50/17.69         ((r2_hidden @ X10 @ X8)
% 17.50/17.69          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 17.50/17.69      inference('simplify', [status(thm)], ['14'])).
% 17.50/17.69  thf('16', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 17.50/17.69          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['13', '15'])).
% 17.50/17.69  thf('17', plain,
% 17.50/17.69      (![X3 : $i, X5 : $i]:
% 17.50/17.69         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 17.50/17.69      inference('cnf', [status(esa)], [d3_tarski])).
% 17.50/17.69  thf('18', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 17.50/17.69          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['16', '17'])).
% 17.50/17.69  thf('19', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.50/17.69      inference('simplify', [status(thm)], ['18'])).
% 17.50/17.69  thf('20', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 17.50/17.69          (k2_zfmisc_1 @ X1 @ X0))),
% 17.50/17.69      inference('sup+', [status(thm)], ['12', '19'])).
% 17.50/17.69  thf('21', plain,
% 17.50/17.69      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.50/17.69      inference('demod', [status(thm)], ['4', '5'])).
% 17.50/17.69  thf('22', plain,
% 17.50/17.69      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 17.50/17.69              (k2_zfmisc_1 @ X31 @ X32)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 17.50/17.69  thf(t117_zfmisc_1, axiom,
% 17.50/17.69    (![A:$i,B:$i,C:$i]:
% 17.50/17.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 17.50/17.69          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 17.50/17.69            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 17.50/17.69          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 17.50/17.69  thf('23', plain,
% 17.50/17.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 17.50/17.69         (((X26) = (k1_xboole_0))
% 17.50/17.69          | (r1_tarski @ X27 @ X28)
% 17.50/17.69          | ~ (r1_tarski @ (k2_zfmisc_1 @ X26 @ X27) @ 
% 17.50/17.69               (k2_zfmisc_1 @ X26 @ X28)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 17.50/17.69  thf('24', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.50/17.69         (~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X1) @ X4) @ 
% 17.50/17.69             (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 17.50/17.69          | (r1_tarski @ X4 @ (k3_xboole_0 @ X2 @ X0))
% 17.50/17.69          | ((k3_xboole_0 @ X3 @ X1) = (k1_xboole_0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['22', '23'])).
% 17.50/17.69  thf('25', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         (~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ X0) @ 
% 17.50/17.69             (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | ((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))
% 17.50/17.69          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['21', '24'])).
% 17.50/17.69  thf('26', plain,
% 17.50/17.69      (((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D_1 @ sk_B))
% 17.50/17.69        | ((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['20', '25'])).
% 17.50/17.69  thf('27', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.50/17.69      inference('simplify', [status(thm)], ['18'])).
% 17.50/17.69  thf('28', plain,
% 17.50/17.69      (![X16 : $i, X18 : $i]:
% 17.50/17.69         (((X16) = (X18))
% 17.50/17.69          | ~ (r1_tarski @ X18 @ X16)
% 17.50/17.69          | ~ (r1_tarski @ X16 @ X18))),
% 17.50/17.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.50/17.69  thf('29', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 17.50/17.69          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['27', '28'])).
% 17.50/17.69  thf('30', plain,
% 17.50/17.69      ((((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))
% 17.50/17.69        | ((sk_B) = (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['26', '29'])).
% 17.50/17.69  thf('31', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.50/17.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.50/17.69  thf('32', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.50/17.69      inference('simplify', [status(thm)], ['18'])).
% 17.50/17.69  thf('33', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 17.50/17.69      inference('sup+', [status(thm)], ['31', '32'])).
% 17.50/17.69  thf('34', plain,
% 17.50/17.69      (((r1_tarski @ sk_B @ sk_D_1)
% 17.50/17.69        | ((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['30', '33'])).
% 17.50/17.69  thf('35', plain,
% 17.50/17.69      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('split', [status(esa)], ['0'])).
% 17.50/17.69  thf('36', plain,
% 17.50/17.69      ((((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0)))
% 17.50/17.69         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['34', '35'])).
% 17.50/17.69  thf('37', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['10', '11'])).
% 17.50/17.69  thf('38', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.50/17.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.50/17.69  thf(t4_xboole_0, axiom,
% 17.50/17.69    (![A:$i,B:$i]:
% 17.50/17.69     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 17.50/17.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 17.50/17.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 17.50/17.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 17.50/17.69  thf('39', plain,
% 17.50/17.69      (![X12 : $i, X13 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X12 @ X13)
% 17.50/17.69          | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 17.50/17.69  thf('40', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X10 @ X9)
% 17.50/17.69          | (r2_hidden @ X10 @ X7)
% 17.50/17.69          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 17.50/17.69      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.50/17.69  thf('41', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X10 : $i]:
% 17.50/17.69         ((r2_hidden @ X10 @ X7)
% 17.50/17.69          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 17.50/17.69      inference('simplify', [status(thm)], ['40'])).
% 17.50/17.69  thf('42', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1))),
% 17.50/17.69      inference('sup-', [status(thm)], ['39', '41'])).
% 17.50/17.69  thf('43', plain,
% 17.50/17.69      (![X12 : $i, X13 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X12 @ X13)
% 17.50/17.69          | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 17.50/17.69  thf('44', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X10 : $i]:
% 17.50/17.69         ((r2_hidden @ X10 @ X8)
% 17.50/17.69          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 17.50/17.69      inference('simplify', [status(thm)], ['14'])).
% 17.50/17.69  thf('45', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['43', '44'])).
% 17.50/17.69  thf('46', plain,
% 17.50/17.69      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 17.50/17.69        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 17.50/17.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.50/17.69  thf('47', plain,
% 17.50/17.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X2 @ X3)
% 17.50/17.69          | (r2_hidden @ X2 @ X4)
% 17.50/17.69          | ~ (r1_tarski @ X3 @ X4))),
% 17.50/17.69      inference('cnf', [status(esa)], [d3_tarski])).
% 17.50/17.69  thf('48', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 17.50/17.69          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['46', '47'])).
% 17.50/17.69  thf('49', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | (r2_hidden @ (sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 17.50/17.69             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['45', '48'])).
% 17.50/17.69  thf('50', plain,
% 17.50/17.69      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X6 @ X7)
% 17.50/17.69          | ~ (r2_hidden @ X6 @ X8)
% 17.50/17.69          | (r2_hidden @ X6 @ X9)
% 17.50/17.69          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 17.50/17.69      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.50/17.69  thf('51', plain,
% 17.50/17.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 17.50/17.69         ((r2_hidden @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 17.50/17.69          | ~ (r2_hidden @ X6 @ X8)
% 17.50/17.69          | ~ (r2_hidden @ X6 @ X7))),
% 17.50/17.69      inference('simplify', [status(thm)], ['50'])).
% 17.50/17.69  thf('52', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | ~ (r2_hidden @ (sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ X1)
% 17.50/17.69          | (r2_hidden @ (sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 17.50/17.69             (k3_xboole_0 @ X1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))))),
% 17.50/17.69      inference('sup-', [status(thm)], ['49', '51'])).
% 17.50/17.69  thf('53', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | (r2_hidden @ (sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 17.50/17.69             (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))
% 17.50/17.69          | (r1_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['42', '52'])).
% 17.50/17.69  thf('54', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         ((r2_hidden @ (sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 17.50/17.69           (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))
% 17.50/17.69          | (r1_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.50/17.69      inference('simplify', [status(thm)], ['53'])).
% 17.50/17.69  thf('55', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['8', '9'])).
% 17.50/17.69  thf('56', plain,
% 17.50/17.69      (![X12 : $i, X14 : $i, X15 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 17.50/17.69          | ~ (r1_xboole_0 @ X12 @ X15))),
% 17.50/17.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 17.50/17.69  thf('57', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['55', '56'])).
% 17.50/17.69  thf('58', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | ~ (r1_xboole_0 @ 
% 17.50/17.69               (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ 
% 17.50/17.69               (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))))),
% 17.50/17.69      inference('sup-', [status(thm)], ['54', '57'])).
% 17.50/17.69  thf('59', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         (~ (r1_xboole_0 @ 
% 17.50/17.69             (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X0) @ 
% 17.50/17.69             (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))
% 17.50/17.69          | (r1_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['38', '58'])).
% 17.50/17.69  thf('60', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         (~ (r1_xboole_0 @ 
% 17.50/17.69             (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 17.50/17.69              (k2_zfmisc_1 @ X0 @ sk_D_1)) @ 
% 17.50/17.69             (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_C_2) @ sk_D_1))
% 17.50/17.69          | (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_D_1) @ 
% 17.50/17.69             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['37', '59'])).
% 17.50/17.69  thf('61', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['10', '11'])).
% 17.50/17.69  thf('62', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         (~ (r1_xboole_0 @ 
% 17.50/17.69             (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ X0) @ sk_D_1) @ 
% 17.50/17.69             (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_C_2) @ sk_D_1))
% 17.50/17.69          | (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_D_1) @ 
% 17.50/17.69             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.50/17.69      inference('demod', [status(thm)], ['60', '61'])).
% 17.50/17.69  thf('63', plain,
% 17.50/17.69      (((~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_D_1) @ 
% 17.50/17.69            (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_2) @ sk_D_1))
% 17.50/17.69         | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D_1) @ 
% 17.50/17.69            (k2_zfmisc_1 @ sk_A @ sk_B))))
% 17.50/17.69         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['36', '62'])).
% 17.50/17.69  thf(t113_zfmisc_1, axiom,
% 17.50/17.69    (![A:$i,B:$i]:
% 17.50/17.69     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 17.50/17.69       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 17.50/17.69  thf('64', plain,
% 17.50/17.69      (![X24 : $i, X25 : $i]:
% 17.50/17.69         (((k2_zfmisc_1 @ X24 @ X25) = (k1_xboole_0))
% 17.50/17.69          | ((X24) != (k1_xboole_0)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 17.50/17.69  thf('65', plain,
% 17.50/17.69      (![X25 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 17.50/17.69      inference('simplify', [status(thm)], ['64'])).
% 17.50/17.69  thf('66', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.50/17.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.50/17.69  thf('67', plain,
% 17.50/17.69      ((((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0)))
% 17.50/17.69         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['34', '35'])).
% 17.50/17.69  thf('68', plain,
% 17.50/17.69      (![X25 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 17.50/17.69      inference('simplify', [status(thm)], ['64'])).
% 17.50/17.69  thf('69', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1))),
% 17.50/17.69      inference('sup-', [status(thm)], ['39', '41'])).
% 17.50/17.69  thf(t2_boole, axiom,
% 17.50/17.69    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 17.50/17.69  thf('70', plain,
% 17.50/17.69      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 17.50/17.69      inference('cnf', [status(esa)], [t2_boole])).
% 17.50/17.69  thf('71', plain,
% 17.50/17.69      (![X12 : $i, X14 : $i, X15 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 17.50/17.69          | ~ (r1_xboole_0 @ X12 @ X15))),
% 17.50/17.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 17.50/17.69  thf('72', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['70', '71'])).
% 17.50/17.69  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 17.50/17.69  thf('73', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 17.50/17.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 17.50/17.69  thf('74', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 17.50/17.69      inference('demod', [status(thm)], ['72', '73'])).
% 17.50/17.69  thf('75', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 17.50/17.69      inference('sup-', [status(thm)], ['69', '74'])).
% 17.50/17.69  thf('76', plain,
% 17.50/17.69      (((r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D_1) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_A @ sk_B))) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('demod', [status(thm)], ['63', '65', '66', '67', '68', '75'])).
% 17.50/17.69  thf('77', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X11 : $i]:
% 17.50/17.69         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 17.50/17.69          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 17.50/17.69          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 17.50/17.69      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.50/17.69  thf('78', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 17.50/17.69      inference('demod', [status(thm)], ['72', '73'])).
% 17.50/17.69  thf('79', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 17.50/17.69          | ((X1) = (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['77', '78'])).
% 17.50/17.69  thf('80', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.50/17.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.50/17.69  thf('81', plain,
% 17.50/17.69      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 17.50/17.69      inference('cnf', [status(esa)], [t2_boole])).
% 17.50/17.69  thf('82', plain,
% 17.50/17.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.50/17.69      inference('sup+', [status(thm)], ['80', '81'])).
% 17.50/17.69  thf('83', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 17.50/17.69          | ((X1) = (k1_xboole_0)))),
% 17.50/17.69      inference('demod', [status(thm)], ['79', '82'])).
% 17.50/17.69  thf('84', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['8', '9'])).
% 17.50/17.69  thf('85', plain,
% 17.50/17.69      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 17.50/17.69              (k2_zfmisc_1 @ X31 @ X32)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 17.50/17.69  thf('86', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['84', '85'])).
% 17.50/17.69  thf('87', plain,
% 17.50/17.69      (![X12 : $i, X14 : $i, X15 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 17.50/17.69          | ~ (r1_xboole_0 @ X12 @ X15))),
% 17.50/17.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 17.50/17.69  thf('88', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 17.50/17.69          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['86', '87'])).
% 17.50/17.69  thf('89', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         (((k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) = (k1_xboole_0))
% 17.50/17.69          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['83', '88'])).
% 17.50/17.69  thf('90', plain,
% 17.50/17.69      ((((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B)) = (k1_xboole_0)))
% 17.50/17.69         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['76', '89'])).
% 17.50/17.69  thf('91', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['10', '11'])).
% 17.50/17.69  thf('92', plain,
% 17.50/17.69      ((![X0 : $i]:
% 17.50/17.69          ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 17.50/17.69            (k3_xboole_0 @ sk_D_1 @ sk_B))
% 17.50/17.69            = (k3_xboole_0 @ k1_xboole_0 @ 
% 17.50/17.69               (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))))
% 17.50/17.69         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['90', '91'])).
% 17.50/17.69  thf('93', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.50/17.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.50/17.69  thf('94', plain,
% 17.50/17.69      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 17.50/17.69              (k2_zfmisc_1 @ X31 @ X32)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 17.50/17.69  thf('95', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X3) @ (k2_zfmisc_1 @ X1 @ X2)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['93', '94'])).
% 17.50/17.69  thf('96', plain,
% 17.50/17.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.50/17.69      inference('sup+', [status(thm)], ['80', '81'])).
% 17.50/17.69  thf('97', plain,
% 17.50/17.69      ((![X0 : $i]:
% 17.50/17.69          ((k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_D_1) @ 
% 17.50/17.69            (k2_zfmisc_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 17.50/17.69         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('demod', [status(thm)], ['92', '95', '96'])).
% 17.50/17.69  thf('98', plain,
% 17.50/17.69      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 17.50/17.69         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['6', '97'])).
% 17.50/17.69  thf('99', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 17.50/17.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.50/17.69  thf('100', plain, (((r1_tarski @ sk_B @ sk_D_1))),
% 17.50/17.69      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 17.50/17.69  thf('101', plain,
% 17.50/17.69      (~ ((r1_tarski @ sk_A @ sk_C_2)) | ~ ((r1_tarski @ sk_B @ sk_D_1))),
% 17.50/17.69      inference('split', [status(esa)], ['0'])).
% 17.50/17.69  thf('102', plain, (~ ((r1_tarski @ sk_A @ sk_C_2))),
% 17.50/17.69      inference('sat_resolution*', [status(thm)], ['100', '101'])).
% 17.50/17.69  thf('103', plain, (~ (r1_tarski @ sk_A @ sk_C_2)),
% 17.50/17.69      inference('simpl_trail', [status(thm)], ['1', '102'])).
% 17.50/17.69  thf('104', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['84', '85'])).
% 17.50/17.69  thf('105', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.50/17.69      inference('simplify', [status(thm)], ['18'])).
% 17.50/17.69  thf('106', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 17.50/17.69          (k2_zfmisc_1 @ X2 @ X0))),
% 17.50/17.69      inference('sup+', [status(thm)], ['104', '105'])).
% 17.50/17.69  thf('107', plain,
% 17.50/17.69      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.50/17.69      inference('demod', [status(thm)], ['4', '5'])).
% 17.50/17.69  thf('108', plain,
% 17.50/17.69      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 17.50/17.69              (k2_zfmisc_1 @ X31 @ X32)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 17.50/17.69  thf('109', plain,
% 17.50/17.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 17.50/17.69         (((X26) = (k1_xboole_0))
% 17.50/17.69          | (r1_tarski @ X27 @ X28)
% 17.50/17.69          | ~ (r1_tarski @ (k2_zfmisc_1 @ X27 @ X26) @ 
% 17.50/17.69               (k2_zfmisc_1 @ X28 @ X26)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 17.50/17.69  thf('110', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.50/17.69         (~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 17.50/17.69             (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 17.50/17.69          | (r1_tarski @ X4 @ (k3_xboole_0 @ X3 @ X1))
% 17.50/17.69          | ((k3_xboole_0 @ X2 @ X0) = (k1_xboole_0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['108', '109'])).
% 17.50/17.69  thf('111', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)) @ 
% 17.50/17.69             (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | ((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 17.50/17.69          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_C_2 @ sk_A)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['107', '110'])).
% 17.50/17.69  thf('112', plain,
% 17.50/17.69      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_2 @ sk_A))
% 17.50/17.69        | ((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['106', '111'])).
% 17.50/17.69  thf('113', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 17.50/17.69          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['27', '28'])).
% 17.50/17.69  thf('114', plain,
% 17.50/17.69      ((((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 17.50/17.69        | ((sk_A) = (k3_xboole_0 @ sk_C_2 @ sk_A)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['112', '113'])).
% 17.50/17.69  thf('115', plain,
% 17.50/17.69      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.50/17.69      inference('demod', [status(thm)], ['4', '5'])).
% 17.50/17.69  thf('116', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 17.50/17.69          | ((X1) = (k1_xboole_0)))),
% 17.50/17.69      inference('demod', [status(thm)], ['79', '82'])).
% 17.50/17.69  thf('117', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X10 : $i]:
% 17.50/17.69         ((r2_hidden @ X10 @ X8)
% 17.50/17.69          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 17.50/17.69      inference('simplify', [status(thm)], ['14'])).
% 17.50/17.69  thf('118', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 17.50/17.69          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 17.50/17.69             X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['116', '117'])).
% 17.50/17.69  thf('119', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         ((r2_hidden @ 
% 17.50/17.69           (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ k1_xboole_0) @ 
% 17.50/17.69           (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 17.50/17.69              (k2_zfmisc_1 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['115', '118'])).
% 17.50/17.69  thf('120', plain,
% 17.50/17.69      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.50/17.69      inference('demod', [status(thm)], ['4', '5'])).
% 17.50/17.69  thf('121', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         ((r2_hidden @ 
% 17.50/17.69           (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ k1_xboole_0) @ 
% 17.50/17.69           (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 17.50/17.69      inference('demod', [status(thm)], ['119', '120'])).
% 17.50/17.69  thf('122', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 17.50/17.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.50/17.69  thf('123', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         (r2_hidden @ 
% 17.50/17.69          (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ k1_xboole_0) @ 
% 17.50/17.69          (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.50/17.69      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 17.50/17.69  thf('124', plain,
% 17.50/17.69      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 17.50/17.69      inference('demod', [status(thm)], ['4', '5'])).
% 17.50/17.69  thf('125', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.50/17.69      inference('simplify', [status(thm)], ['18'])).
% 17.50/17.69  thf('126', plain,
% 17.50/17.69      (![X19 : $i, X20 : $i]:
% 17.50/17.69         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 17.50/17.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.50/17.69  thf('127', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 17.50/17.69           = (k3_xboole_0 @ X1 @ X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['125', '126'])).
% 17.50/17.69  thf('128', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.50/17.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.50/17.69  thf('129', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 17.50/17.69           = (k3_xboole_0 @ X1 @ X0))),
% 17.50/17.69      inference('demod', [status(thm)], ['127', '128'])).
% 17.50/17.69  thf('130', plain,
% 17.50/17.69      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 17.50/17.69              (k2_zfmisc_1 @ X31 @ X32)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 17.50/17.69  thf('131', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X3) @ 
% 17.50/17.69              (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['129', '130'])).
% 17.50/17.69  thf('132', plain,
% 17.50/17.69      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ (k3_xboole_0 @ X29 @ X31) @ (k3_xboole_0 @ X30 @ X32))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 17.50/17.69              (k2_zfmisc_1 @ X31 @ X32)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 17.50/17.69  thf('133', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.50/17.69         ((k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X3) @ (k2_zfmisc_1 @ X0 @ X2))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X3) @ 
% 17.50/17.69              (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 17.50/17.69      inference('demod', [status(thm)], ['131', '132'])).
% 17.50/17.69  thf('134', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X10 : $i]:
% 17.50/17.69         ((r2_hidden @ X10 @ X7)
% 17.50/17.69          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 17.50/17.69      inference('simplify', [status(thm)], ['40'])).
% 17.50/17.69  thf('135', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X4 @ 
% 17.50/17.69             (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 17.50/17.69          | (r2_hidden @ X4 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['133', '134'])).
% 17.50/17.69  thf('136', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 17.50/17.69          | (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_D_1)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['124', '135'])).
% 17.50/17.69  thf('137', plain,
% 17.50/17.69      (![X0 : $i]:
% 17.50/17.69         (r2_hidden @ 
% 17.50/17.69          (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0 @ k1_xboole_0) @ 
% 17.50/17.69          (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 17.50/17.69      inference('sup-', [status(thm)], ['123', '136'])).
% 17.50/17.69  thf('138', plain,
% 17.50/17.69      (![X7 : $i, X8 : $i, X11 : $i]:
% 17.50/17.69         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 17.50/17.69          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 17.50/17.69          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 17.50/17.69      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.50/17.69  thf('139', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 17.50/17.69      inference('demod', [status(thm)], ['72', '73'])).
% 17.50/17.69  thf('140', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 17.50/17.69          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['138', '139'])).
% 17.50/17.69  thf('141', plain,
% 17.50/17.69      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 17.50/17.69      inference('cnf', [status(esa)], [t2_boole])).
% 17.50/17.69  thf('142', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 17.50/17.69          | ((X1) = (k1_xboole_0)))),
% 17.50/17.69      inference('demod', [status(thm)], ['140', '141'])).
% 17.50/17.69  thf('143', plain,
% 17.50/17.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 17.50/17.69         ((r2_hidden @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 17.50/17.69          | ~ (r2_hidden @ X6 @ X8)
% 17.50/17.69          | ~ (r2_hidden @ X6 @ X7))),
% 17.50/17.69      inference('simplify', [status(thm)], ['50'])).
% 17.50/17.69  thf('144', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         (((X0) = (k1_xboole_0))
% 17.50/17.69          | ~ (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X2)
% 17.50/17.69          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ 
% 17.50/17.69             (k3_xboole_0 @ X2 @ X0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['142', '143'])).
% 17.50/17.69  thf('145', plain,
% 17.50/17.69      (((r2_hidden @ 
% 17.50/17.69         (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ k1_xboole_0 @ k1_xboole_0) @ 
% 17.50/17.69         (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D_1) @ 
% 17.50/17.69          (k2_zfmisc_1 @ sk_A @ sk_B)))
% 17.50/17.69        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['137', '144'])).
% 17.50/17.69  thf('146', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.50/17.69         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 17.50/17.69           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 17.50/17.69      inference('sup+', [status(thm)], ['84', '85'])).
% 17.50/17.69  thf('147', plain,
% 17.50/17.69      (((r2_hidden @ 
% 17.50/17.69         (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ k1_xboole_0 @ k1_xboole_0) @ 
% 17.50/17.69         (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B)))
% 17.50/17.69        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 17.50/17.69      inference('demod', [status(thm)], ['145', '146'])).
% 17.50/17.69  thf('148', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 17.50/17.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.50/17.69  thf('149', plain,
% 17.50/17.69      ((r2_hidden @ 
% 17.50/17.69        (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ k1_xboole_0 @ k1_xboole_0) @ 
% 17.50/17.69        (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 17.50/17.69      inference('simplify_reflect-', [status(thm)], ['147', '148'])).
% 17.50/17.69  thf('150', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]:
% 17.50/17.69         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 17.50/17.69      inference('sup-', [status(thm)], ['55', '56'])).
% 17.50/17.69  thf('151', plain,
% 17.50/17.69      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B)) @ 
% 17.50/17.69          (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['149', '150'])).
% 17.50/17.69  thf('152', plain,
% 17.50/17.69      ((~ (r1_xboole_0 @ 
% 17.50/17.69           (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B)) @ 
% 17.50/17.69           (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 17.50/17.69        | ((sk_A) = (k3_xboole_0 @ sk_C_2 @ sk_A)))),
% 17.50/17.69      inference('sup-', [status(thm)], ['114', '151'])).
% 17.50/17.69  thf('153', plain,
% 17.50/17.69      (![X24 : $i, X25 : $i]:
% 17.50/17.69         (((k2_zfmisc_1 @ X24 @ X25) = (k1_xboole_0))
% 17.50/17.69          | ((X25) != (k1_xboole_0)))),
% 17.50/17.69      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 17.50/17.69  thf('154', plain,
% 17.50/17.69      (![X24 : $i]: ((k2_zfmisc_1 @ X24 @ k1_xboole_0) = (k1_xboole_0))),
% 17.50/17.69      inference('simplify', [status(thm)], ['153'])).
% 17.50/17.69  thf('155', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 17.50/17.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 17.50/17.69  thf('156', plain, (((sk_A) = (k3_xboole_0 @ sk_C_2 @ sk_A))),
% 17.50/17.69      inference('demod', [status(thm)], ['152', '154', '155'])).
% 17.50/17.69  thf('157', plain,
% 17.50/17.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 17.50/17.69      inference('sup+', [status(thm)], ['31', '32'])).
% 17.50/17.69  thf('158', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 17.50/17.69      inference('sup+', [status(thm)], ['156', '157'])).
% 17.50/17.69  thf('159', plain, ($false), inference('demod', [status(thm)], ['103', '158'])).
% 17.50/17.69  
% 17.50/17.69  % SZS output end Refutation
% 17.50/17.69  
% 17.50/17.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
