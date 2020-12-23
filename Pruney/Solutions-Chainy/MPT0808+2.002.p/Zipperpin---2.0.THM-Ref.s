%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kM7SlzVR4L

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:37 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 100 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  605 (1822 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r3_wellord1 @ X9 @ X8 @ X10 )
      | ( ( k9_relat_1 @ X10 @ ( k1_wellord1 @ X9 @ X11 ) )
        = ( k1_wellord1 @ X8 @ ( sk_E @ X11 @ X10 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X12: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ sk_D ) ) @ ( k2_wellord1 @ sk_B @ ( k1_wellord1 @ sk_B @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ sk_D ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ sk_D ) ) ) )
    | ~ ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
          = ( k1_wellord1 @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v2_wellord1 @ X2 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X3 ) ) )
        = ( k1_wellord1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( k3_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

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

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v2_wellord1 @ X5 )
      | ~ ( r1_tarski @ X6 @ ( k3_relat_1 @ X5 ) )
      | ~ ( r3_wellord1 @ X5 @ X4 @ X7 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X5 @ X6 ) @ ( k2_wellord1 @ X4 @ ( k9_relat_1 @ X7 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t59_wellord1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k2_wellord1 @ X3 @ ( k9_relat_1 @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) )
      | ~ ( r3_wellord1 @ X0 @ X3 @ X2 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r3_wellord1 @ X0 @ X3 @ X2 )
      | ( r4_wellord1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) @ ( k2_wellord1 @ X3 @ ( k9_relat_1 @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v2_wellord1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ X0 ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( r4_wellord1 @ ( k2_wellord1 @ sk_A @ ( k1_wellord1 @ sk_A @ X0 ) ) @ ( k2_wellord1 @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_wellord1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26'])).

thf('28',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_D @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r3_wellord1 @ X9 @ X8 @ X10 )
      | ( r2_hidden @ ( sk_E @ X11 @ X10 @ X8 @ X9 ) @ ( k3_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t60_wellord1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ X1 @ sk_A ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['12','27','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kM7SlzVR4L
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 11:45:53 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 46 iterations in 0.041s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.24/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.24/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.49  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.24/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.24/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.24/0.49  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.24/0.49  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.49  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.24/0.49  thf(t61_wellord1, conjecture,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ A ) =>
% 0.24/0.49       ( ![B:$i]:
% 0.24/0.49         ( ( v1_relat_1 @ B ) =>
% 0.24/0.49           ( ![C:$i]:
% 0.24/0.49             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.49               ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.24/0.49                 ( ![D:$i]:
% 0.24/0.49                   ( ~( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.24/0.49                        ( ![E:$i]:
% 0.24/0.49                          ( ~( ( r2_hidden @ E @ ( k3_relat_1 @ B ) ) & 
% 0.24/0.49                               ( r4_wellord1 @
% 0.24/0.49                                 ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ D ) ) @ 
% 0.24/0.49                                 ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i]:
% 0.24/0.49        ( ( v1_relat_1 @ A ) =>
% 0.24/0.49          ( ![B:$i]:
% 0.24/0.49            ( ( v1_relat_1 @ B ) =>
% 0.24/0.49              ( ![C:$i]:
% 0.24/0.49                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.49                  ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.24/0.49                    ( ![D:$i]:
% 0.24/0.49                      ( ~( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.24/0.49                           ( ![E:$i]:
% 0.24/0.49                             ( ~( ( r2_hidden @ E @ ( k3_relat_1 @ B ) ) & 
% 0.24/0.49                                  ( r4_wellord1 @
% 0.24/0.49                                    ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ D ) ) @ 
% 0.24/0.49                                    ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t61_wellord1])).
% 0.24/0.49  thf('0', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('1', plain, ((r2_hidden @ sk_D @ (k3_relat_1 @ sk_A))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(t60_wellord1, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ A ) =>
% 0.24/0.49       ( ![B:$i]:
% 0.24/0.49         ( ( v1_relat_1 @ B ) =>
% 0.24/0.49           ( ![C:$i]:
% 0.24/0.49             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.49               ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.24/0.49                 ( ![D:$i]:
% 0.24/0.49                   ( ~( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.24/0.49                        ( ![E:$i]:
% 0.24/0.49                          ( ~( ( r2_hidden @ E @ ( k3_relat_1 @ B ) ) & 
% 0.24/0.49                               ( ( k9_relat_1 @ C @ ( k1_wellord1 @ A @ D ) ) =
% 0.24/0.49                                 ( k1_wellord1 @ B @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ X8)
% 0.24/0.49          | ~ (r3_wellord1 @ X9 @ X8 @ X10)
% 0.24/0.49          | ((k9_relat_1 @ X10 @ (k1_wellord1 @ X9 @ X11))
% 0.24/0.49              = (k1_wellord1 @ X8 @ (sk_E @ X11 @ X10 @ X8 @ X9)))
% 0.24/0.49          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X9))
% 0.24/0.49          | ~ (v1_funct_1 @ X10)
% 0.24/0.49          | ~ (v1_relat_1 @ X10)
% 0.24/0.49          | ~ (v1_relat_1 @ X9))),
% 0.24/0.49      inference('cnf', [status(esa)], [t60_wellord1])).
% 0.24/0.49  thf('3', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ sk_A)
% 0.24/0.49          | ~ (v1_relat_1 @ X0)
% 0.24/0.49          | ~ (v1_funct_1 @ X0)
% 0.24/0.49          | ((k9_relat_1 @ X0 @ (k1_wellord1 @ sk_A @ sk_D))
% 0.24/0.49              = (k1_wellord1 @ X1 @ (sk_E @ sk_D @ X0 @ X1 @ sk_A)))
% 0.24/0.49          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ X1))),
% 0.24/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.49  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ X0)
% 0.24/0.49          | ~ (v1_funct_1 @ X0)
% 0.24/0.49          | ((k9_relat_1 @ X0 @ (k1_wellord1 @ sk_A @ sk_D))
% 0.24/0.49              = (k1_wellord1 @ X1 @ (sk_E @ sk_D @ X0 @ X1 @ sk_A)))
% 0.24/0.49          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ X1))),
% 0.24/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.24/0.49  thf('6', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.24/0.49        | ((k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ sk_D))
% 0.24/0.49            = (k1_wellord1 @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['0', '5'])).
% 0.24/0.49  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('10', plain,
% 0.24/0.49      (((k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ sk_D))
% 0.24/0.49         = (k1_wellord1 @ sk_B @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.24/0.49      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.24/0.49  thf('11', plain,
% 0.24/0.49      (![X12 : $i]:
% 0.24/0.49         (~ (r2_hidden @ X12 @ (k3_relat_1 @ sk_B))
% 0.24/0.49          | ~ (r4_wellord1 @ 
% 0.24/0.49               (k2_wellord1 @ sk_A @ (k1_wellord1 @ sk_A @ sk_D)) @ 
% 0.24/0.49               (k2_wellord1 @ sk_B @ (k1_wellord1 @ sk_B @ X12))))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('12', plain,
% 0.24/0.49      ((~ (r4_wellord1 @ (k2_wellord1 @ sk_A @ (k1_wellord1 @ sk_A @ sk_D)) @ 
% 0.24/0.49           (k2_wellord1 @ sk_B @ 
% 0.24/0.49            (k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ sk_D))))
% 0.24/0.49        | ~ (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.24/0.49             (k3_relat_1 @ sk_B)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.49  thf('13', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(t40_wellord1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ B ) =>
% 0.24/0.49       ( ( v2_wellord1 @ B ) =>
% 0.24/0.49         ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) ) =
% 0.24/0.49           ( k1_wellord1 @ B @ A ) ) ) ))).
% 0.24/0.49  thf('14', plain,
% 0.24/0.49      (![X2 : $i, X3 : $i]:
% 0.24/0.49         (~ (v2_wellord1 @ X2)
% 0.24/0.49          | ((k3_relat_1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X3)))
% 0.24/0.49              = (k1_wellord1 @ X2 @ X3))
% 0.24/0.49          | ~ (v1_relat_1 @ X2))),
% 0.24/0.49      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.24/0.49  thf(t20_wellord1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ B ) =>
% 0.24/0.49       ( ( r1_tarski @
% 0.24/0.49           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.24/0.49         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.24/0.49  thf('15', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ 
% 0.24/0.49           (k3_relat_1 @ X0))
% 0.24/0.49          | ~ (v1_relat_1 @ X0))),
% 0.24/0.49      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.24/0.49  thf('16', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ (k3_relat_1 @ X1))
% 0.24/0.49          | ~ (v1_relat_1 @ X1)
% 0.24/0.49          | ~ (v2_wellord1 @ X1)
% 0.24/0.49          | ~ (v1_relat_1 @ X1))),
% 0.24/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.24/0.49  thf('17', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (v2_wellord1 @ X1)
% 0.24/0.49          | ~ (v1_relat_1 @ X1)
% 0.24/0.49          | (r1_tarski @ (k1_wellord1 @ X1 @ X0) @ (k3_relat_1 @ X1)))),
% 0.24/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.24/0.49  thf(t59_wellord1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ B ) =>
% 0.24/0.49       ( ![C:$i]:
% 0.24/0.49         ( ( v1_relat_1 @ C ) =>
% 0.24/0.49           ( ![D:$i]:
% 0.24/0.49             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.24/0.49               ( ( ( v2_wellord1 @ B ) & 
% 0.24/0.49                   ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) & 
% 0.24/0.49                   ( r3_wellord1 @ B @ C @ D ) ) =>
% 0.24/0.49                 ( ( r3_wellord1 @
% 0.24/0.49                     ( k2_wellord1 @ B @ A ) @ 
% 0.24/0.49                     ( k2_wellord1 @ C @ ( k9_relat_1 @ D @ A ) ) @ 
% 0.24/0.49                     ( k7_relat_1 @ D @ A ) ) & 
% 0.24/0.49                   ( r4_wellord1 @
% 0.24/0.49                     ( k2_wellord1 @ B @ A ) @ 
% 0.24/0.49                     ( k2_wellord1 @ C @ ( k9_relat_1 @ D @ A ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.49  thf('18', plain,
% 0.24/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ X4)
% 0.24/0.49          | ~ (v2_wellord1 @ X5)
% 0.24/0.49          | ~ (r1_tarski @ X6 @ (k3_relat_1 @ X5))
% 0.24/0.49          | ~ (r3_wellord1 @ X5 @ X4 @ X7)
% 0.24/0.49          | (r4_wellord1 @ (k2_wellord1 @ X5 @ X6) @ 
% 0.24/0.49             (k2_wellord1 @ X4 @ (k9_relat_1 @ X7 @ X6)))
% 0.24/0.49          | ~ (v1_funct_1 @ X7)
% 0.24/0.49          | ~ (v1_relat_1 @ X7)
% 0.24/0.49          | ~ (v1_relat_1 @ X5))),
% 0.24/0.49      inference('cnf', [status(esa)], [t59_wellord1])).
% 0.24/0.49  thf('19', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ X0)
% 0.24/0.49          | ~ (v2_wellord1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ X2)
% 0.24/0.49          | ~ (v1_funct_1 @ X2)
% 0.24/0.49          | (r4_wellord1 @ (k2_wellord1 @ X0 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.24/0.49             (k2_wellord1 @ X3 @ (k9_relat_1 @ X2 @ (k1_wellord1 @ X0 @ X1))))
% 0.24/0.49          | ~ (r3_wellord1 @ X0 @ X3 @ X2)
% 0.24/0.49          | ~ (v2_wellord1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ X3))),
% 0.24/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.49  thf('20', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ X3)
% 0.24/0.49          | ~ (r3_wellord1 @ X0 @ X3 @ X2)
% 0.24/0.49          | (r4_wellord1 @ (k2_wellord1 @ X0 @ (k1_wellord1 @ X0 @ X1)) @ 
% 0.24/0.49             (k2_wellord1 @ X3 @ (k9_relat_1 @ X2 @ (k1_wellord1 @ X0 @ X1))))
% 0.24/0.49          | ~ (v1_funct_1 @ X2)
% 0.24/0.49          | ~ (v1_relat_1 @ X2)
% 0.24/0.49          | ~ (v2_wellord1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ X0))),
% 0.24/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.24/0.49  thf('21', plain,
% 0.24/0.49      (![X0 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ sk_A)
% 0.24/0.49          | ~ (v2_wellord1 @ sk_A)
% 0.24/0.49          | ~ (v1_relat_1 @ sk_C)
% 0.24/0.49          | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49          | (r4_wellord1 @ (k2_wellord1 @ sk_A @ (k1_wellord1 @ sk_A @ X0)) @ 
% 0.24/0.49             (k2_wellord1 @ sk_B @ 
% 0.24/0.49              (k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ X0))))
% 0.24/0.49          | ~ (v1_relat_1 @ sk_B))),
% 0.24/0.49      inference('sup-', [status(thm)], ['13', '20'])).
% 0.24/0.49  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('23', plain, ((v2_wellord1 @ sk_A)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('27', plain,
% 0.24/0.49      (![X0 : $i]:
% 0.24/0.49         (r4_wellord1 @ (k2_wellord1 @ sk_A @ (k1_wellord1 @ sk_A @ X0)) @ 
% 0.24/0.49          (k2_wellord1 @ sk_B @ (k9_relat_1 @ sk_C @ (k1_wellord1 @ sk_A @ X0))))),
% 0.24/0.49      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '26'])).
% 0.24/0.49  thf('28', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('29', plain, ((r2_hidden @ sk_D @ (k3_relat_1 @ sk_A))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('30', plain,
% 0.24/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ X8)
% 0.24/0.49          | ~ (r3_wellord1 @ X9 @ X8 @ X10)
% 0.24/0.49          | (r2_hidden @ (sk_E @ X11 @ X10 @ X8 @ X9) @ (k3_relat_1 @ X8))
% 0.24/0.49          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X9))
% 0.24/0.49          | ~ (v1_funct_1 @ X10)
% 0.24/0.49          | ~ (v1_relat_1 @ X10)
% 0.24/0.49          | ~ (v1_relat_1 @ X9))),
% 0.24/0.49      inference('cnf', [status(esa)], [t60_wellord1])).
% 0.24/0.49  thf('31', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ sk_A)
% 0.24/0.49          | ~ (v1_relat_1 @ X0)
% 0.24/0.49          | ~ (v1_funct_1 @ X0)
% 0.24/0.49          | (r2_hidden @ (sk_E @ sk_D @ X0 @ X1 @ sk_A) @ (k3_relat_1 @ X1))
% 0.24/0.49          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ X1))),
% 0.24/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.24/0.49  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('33', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (v1_relat_1 @ X0)
% 0.24/0.49          | ~ (v1_funct_1 @ X0)
% 0.24/0.49          | (r2_hidden @ (sk_E @ sk_D @ X0 @ X1 @ sk_A) @ (k3_relat_1 @ X1))
% 0.24/0.49          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.24/0.49          | ~ (v1_relat_1 @ X1))),
% 0.24/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.24/0.49  thf('34', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.24/0.49        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ (k3_relat_1 @ sk_B))
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['28', '33'])).
% 0.24/0.49  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('38', plain,
% 0.24/0.49      ((r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ (k3_relat_1 @ sk_B))),
% 0.24/0.49      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.24/0.49  thf('39', plain, ($false),
% 0.24/0.49      inference('demod', [status(thm)], ['12', '27', '38'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
