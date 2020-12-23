%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s3sH876MWn

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  96 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  545 (1762 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(t61_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( v2_wellord1 @ A )
                  & ( r3_wellord1 @ A @ B @ C ) )
               => ! [D: $i] :
                    ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                      & ! [E: $i] :
                          ~ ( ( r2_hidden @ E @ ( k3_relat_1 @ B ) )
                            & ( r4_wellord1 @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ D ) ) @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( v2_wellord1 @ A )
                    & ( r3_wellord1 @ A @ B @ C ) )
                 => ! [D: $i] :
                      ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                        & ! [E: $i] :
                            ~ ( ( r2_hidden @ E @ ( k3_relat_1 @ B ) )
                              & ( r4_wellord1 @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ D ) ) @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_wellord1])).

thf('0',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_D @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
               => ! [D: $i] :
                    ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                      & ! [E: $i] :
                          ~ ( ( r2_hidden @ E @ ( k3_relat_1 @ B ) )
                            & ( ( k9_relat_1 @ C @ ( k1_wellord1 @ A @ D ) )
                              = ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r3_wellord1 @ X7 @ X6 @ X8 )
      | ( ( k9_relat_1 @ X8 @ ( k1_wellord1 @ X7 @ X9 ) )
        = ( k1_wellord1 @ X6 @ ( sk_E @ X9 @ X8 @ X6 @ X7 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t60_wellord1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_wellord1 @ sk_A @ sk_D ) )
        = ( k1_wellord1 @ X1 @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_wellord1 @ sk_A @ sk_D ) )
        = ( k1_wellord1 @ X1 @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ sk_D ) )
      = ( k1_wellord1 @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ sk_D ) )
    = ( k1_wellord1 @ sk_B @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ! [X10: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ sk_D ) ) @ ( k2_wellord1 @ sk_B @ ( k1_wellord1 @ sk_B @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ sk_D ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ sk_D ) ) ) )
    | ~ ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf(t59_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( v2_wellord1 @ B )
                  & ( r1_tarski @ A @ ( k3_relat_1 @ B ) )
                  & ( r3_wellord1 @ B @ C @ D ) )
               => ( ( r3_wellord1 @ ( k2_wellord1 @ B @ A ) @ ( k2_wellord1 @ C @ ( k9_relat_1 @ D @ A ) ) @ ( k7_relat_1 @ D @ A ) )
                  & ( r4_wellord1 @ ( k2_wellord1 @ B @ A ) @ ( k2_wellord1 @ C @ ( k9_relat_1 @ D @ A ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v2_wellord1 @ X3 )
      | ~ ( r1_tarski @ X4 @ ( k3_relat_1 @ X3 ) )
      | ~ ( r3_wellord1 @ X3 @ X2 @ X5 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X3 @ X4 ) @ ( k2_wellord1 @ X2 @ ( k9_relat_1 @ X5 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t59_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k2_wellord1 @ X3 @ ( k9_relat_1 @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) )
      | ~ ( r3_wellord1 @ X0 @ X3 @ X2 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( r3_wellord1 @ X0 @ X3 @ X2 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k2_wellord1 @ X3 @ ( k9_relat_1 @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ X0 ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ X0 ) ) ) )
      | ~ ( v2_wellord1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ X0 ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23'])).

thf('25',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ sk_D @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r3_wellord1 @ X7 @ X6 @ X8 )
      | ( r2_hidden @ ( sk_E @ X9 @ X8 @ X6 @ X7 ) @ ( k3_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t60_wellord1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['12','24','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s3sH876MWn
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 21 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.47  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.47  thf(t61_wellord1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ B ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47               ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.20/0.47                 ( ![D:$i]:
% 0.20/0.47                   ( ~( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.47                        ( ![E:$i]:
% 0.20/0.47                          ( ~( ( r2_hidden @ E @ ( k3_relat_1 @ B ) ) & 
% 0.20/0.47                               ( r4_wellord1 @
% 0.20/0.47                                 ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ D ) ) @ 
% 0.20/0.47                                 ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( v1_relat_1 @ A ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( v1_relat_1 @ B ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47                  ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.20/0.47                    ( ![D:$i]:
% 0.20/0.47                      ( ~( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.47                           ( ![E:$i]:
% 0.20/0.47                             ( ~( ( r2_hidden @ E @ ( k3_relat_1 @ B ) ) & 
% 0.20/0.47                                  ( r4_wellord1 @
% 0.20/0.47                                    ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ D ) ) @ 
% 0.20/0.47                                    ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t61_wellord1])).
% 0.20/0.47  thf('0', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r2_hidden @ sk_D @ (k3_relat_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t60_wellord1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ B ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47               ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.20/0.47                 ( ![D:$i]:
% 0.20/0.47                   ( ~( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.47                        ( ![E:$i]:
% 0.20/0.47                          ( ~( ( r2_hidden @ E @ ( k3_relat_1 @ B ) ) & 
% 0.20/0.47                               ( ( k9_relat_1 @ C @ ( k1_wellord1 @ A @ D ) ) =
% 0.20/0.47                                 ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X6)
% 0.20/0.47          | ~ (r3_wellord1 @ X7 @ X6 @ X8)
% 0.20/0.47          | ((k9_relat_1 @ X8 @ (k1_wellord1 @ X7 @ X9))
% 0.20/0.47              = (k1_wellord1 @ X6 @ (sk_E @ X9 @ X8 @ X6 @ X7)))
% 0.20/0.47          | ~ (r2_hidden @ X9 @ (k3_relat_1 @ X7))
% 0.20/0.47          | ~ (v1_funct_1 @ X8)
% 0.20/0.47          | ~ (v1_relat_1 @ X8)
% 0.20/0.47          | ~ (v1_relat_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t60_wellord1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ sk_A)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ((k9_relat_1 @ X0 @ (k1_wellord1 @ sk_A @ sk_D))
% 0.20/0.47              = (k1_wellord1 @ X1 @ (sk_E @ sk_D @ X0 @ X1 @ sk_A)))
% 0.20/0.47          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ((k9_relat_1 @ X0 @ (k1_wellord1 @ sk_A @ sk_D))
% 0.20/0.47              = (k1_wellord1 @ X1 @ (sk_E @ sk_D @ X0 @ X1 @ sk_A)))
% 0.20/0.47          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ((k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ sk_D))
% 0.20/0.47            = (k1_wellord1 @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.20/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.47  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ sk_D))
% 0.20/0.47         = (k1_wellord1 @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X10 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X10 @ (k3_relat_1 @ sk_B))
% 0.20/0.47          | ~ (r4_wellord1 @ 
% 0.20/0.47               (k2_wellord1 @ sk_A @ (k1_wellord1 @ sk_A @ sk_D)) @ 
% 0.20/0.47               (k2_wellord1 @ sk_B @ (k1_wellord1 @ sk_B @ X10))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((~ (r4_wellord1 @ (k2_wellord1 @ sk_A @ (k1_wellord1 @ sk_A @ sk_D)) @ 
% 0.20/0.47           (k2_wellord1 @ sk_B @ 
% 0.20/0.47            (k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ sk_D))))
% 0.20/0.47        | ~ (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47             (k3_relat_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t13_wellord1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_wellord1 @ X0 @ X1) @ (k3_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t13_wellord1])).
% 0.20/0.47  thf(t59_wellord1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ C ) =>
% 0.20/0.47           ( ![D:$i]:
% 0.20/0.47             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.20/0.47               ( ( ( v2_wellord1 @ B ) & 
% 0.20/0.47                   ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) & 
% 0.20/0.47                   ( r3_wellord1 @ B @ C @ D ) ) =>
% 0.20/0.47                 ( ( r3_wellord1 @
% 0.20/0.47                     ( k2_wellord1 @ B @ A ) @ 
% 0.20/0.47                     ( k2_wellord1 @ C @ ( k9_relat_1 @ D @ A ) ) @ 
% 0.20/0.47                     ( k7_relat_1 @ D @ A ) ) & 
% 0.20/0.47                   ( r4_wellord1 @
% 0.20/0.47                     ( k2_wellord1 @ B @ A ) @ 
% 0.20/0.47                     ( k2_wellord1 @ C @ ( k9_relat_1 @ D @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X2)
% 0.20/0.47          | ~ (v2_wellord1 @ X3)
% 0.20/0.47          | ~ (r1_tarski @ X4 @ (k3_relat_1 @ X3))
% 0.20/0.47          | ~ (r3_wellord1 @ X3 @ X2 @ X5)
% 0.20/0.47          | (r4_wellord1 @ (k2_wellord1 @ X3 @ X4) @ 
% 0.20/0.47             (k2_wellord1 @ X2 @ (k9_relat_1 @ X5 @ X4)))
% 0.20/0.47          | ~ (v1_funct_1 @ X5)
% 0.20/0.47          | ~ (v1_relat_1 @ X5)
% 0.20/0.47          | ~ (v1_relat_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t59_wellord1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X2)
% 0.20/0.47          | ~ (v1_funct_1 @ X2)
% 0.20/0.47          | (r4_wellord1 @ (k2_wellord1 @ X0 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.20/0.47             (k2_wellord1 @ X3 @ (k9_relat_1 @ X2 @ (k1_wellord1 @ X0 @ X1))))
% 0.20/0.47          | ~ (r3_wellord1 @ X0 @ X3 @ X2)
% 0.20/0.47          | ~ (v2_wellord1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X3))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X3)
% 0.20/0.47          | ~ (v2_wellord1 @ X0)
% 0.20/0.47          | ~ (r3_wellord1 @ X0 @ X3 @ X2)
% 0.20/0.47          | (r4_wellord1 @ (k2_wellord1 @ X0 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.20/0.47             (k2_wellord1 @ X3 @ (k9_relat_1 @ X2 @ (k1_wellord1 @ X0 @ X1))))
% 0.20/0.47          | ~ (v1_funct_1 @ X2)
% 0.20/0.47          | ~ (v1_relat_1 @ X2)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ sk_A)
% 0.20/0.47          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47          | (r4_wellord1 @ (k2_wellord1 @ sk_A @ (k1_wellord1 @ sk_A @ X0)) @ 
% 0.20/0.47             (k2_wellord1 @ sk_B @ 
% 0.20/0.47              (k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ X0))))
% 0.20/0.47          | ~ (v2_wellord1 @ sk_A)
% 0.20/0.47          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '17'])).
% 0.20/0.47  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain, ((v2_wellord1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (r4_wellord1 @ (k2_wellord1 @ sk_A @ (k1_wellord1 @ sk_A @ X0)) @ 
% 0.20/0.47          (k2_wellord1 @ sk_B @ (k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ X0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '23'])).
% 0.20/0.47  thf('25', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain, ((r2_hidden @ sk_D @ (k3_relat_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X6)
% 0.20/0.47          | ~ (r3_wellord1 @ X7 @ X6 @ X8)
% 0.20/0.47          | (r2_hidden @ (sk_E @ X9 @ X8 @ X6 @ X7) @ (k3_relat_1 @ X6))
% 0.20/0.47          | ~ (r2_hidden @ X9 @ (k3_relat_1 @ X7))
% 0.20/0.47          | ~ (v1_funct_1 @ X8)
% 0.20/0.47          | ~ (v1_relat_1 @ X8)
% 0.20/0.47          | ~ (v1_relat_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t60_wellord1])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ sk_A)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | (r2_hidden @ (sk_E @ sk_D @ X0 @ X1 @ sk_A) @ (k3_relat_1 @ X1))
% 0.20/0.47          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | (r2_hidden @ (sk_E @ sk_D @ X0 @ X1 @ sk_A) @ (k3_relat_1 @ X1))
% 0.20/0.47          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.20/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '30'])).
% 0.20/0.47  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.20/0.47  thf('36', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '24', '35'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
