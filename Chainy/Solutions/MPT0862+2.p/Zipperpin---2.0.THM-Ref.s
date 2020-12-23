%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0862+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r1kgBwXeWJ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  78 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  269 ( 728 expanded)
%              Number of equality atoms :   40 ( 104 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_93_type,type,(
    sk_D_93: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_72_type,type,(
    sk_B_72: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k1_tarski @ B @ ( k2_tarski @ ( C @ D ) ) ) ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k1_tarski @ B @ ( k2_tarski @ ( C @ D ) ) ) ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_72 @ ( k2_tarski @ ( sk_C_93 @ sk_D_93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X3850 @ X3852 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ ( k2_tarski @ ( sk_C_93 @ sk_D_93 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X441: $i,X443: $i,X444: $i,X445: $i] :
      ( ~ ( r2_hidden @ ( X445 @ X443 ) )
      | ( X445 = X444 )
      | ( X445 = X441 )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X441: $i,X444: $i,X445: $i] :
      ( ( X445 = X441 )
      | ( X445 = X444 )
      | ~ ( r2_hidden @ ( X445 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
      = sk_C_93 )
    | ( ( k2_mcart_1 @ sk_A_14 )
      = sk_D_93 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
    | ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 )
   <= ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_72 @ ( k2_tarski @ ( sk_C_93 @ sk_D_93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X3850 @ X3851 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ ( k1_tarski @ sk_B_72 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('11',plain,(
    ! [X1021: $i,X1023: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1021 @ X1023 ) )
      | ~ ( r2_hidden @ ( X1021 @ X1023 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_mcart_1 @ sk_A_14 ) @ ( k1_tarski @ sk_B_72 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
     => ( A = B ) ) )).

thf('13',plain,(
    ! [X1263: $i,X1264: $i] :
      ( ( X1264 = X1263 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1264 @ ( k1_tarski @ X1263 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_zfmisc_1])).

thf('14',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = sk_B_72 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
    | ( ( k2_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B_72 != sk_B_72 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = sk_B_72 ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_D_93 )
    | ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['6'])).

thf('20',plain,(
    ( k2_mcart_1 @ sk_A_14 )
 != sk_D_93 ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ( k2_mcart_1 @ sk_A_14 )
 != sk_D_93 ),
    inference(simpl_trail,[status(thm)],['7','20'])).

thf('22',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_C_93 )
   <= ( ( k2_mcart_1 @ sk_A_14 )
     != sk_C_93 ) ),
    inference(split,[status(esa)],['15'])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A_14 )
     != sk_C_93 )
    | ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['15'])).

thf('24',plain,(
    ( k2_mcart_1 @ sk_A_14 )
 != sk_C_93 ),
    inference('sat_resolution*',[status(thm)],['18','23'])).

thf('25',plain,(
    ( k2_mcart_1 @ sk_A_14 )
 != sk_C_93 ),
    inference(simpl_trail,[status(thm)],['22','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['5','21','25'])).

%------------------------------------------------------------------------------
