%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PQm1XtGroh

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 220 expanded)
%              Number of leaves         :   24 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  625 (4476 expanded)
%              Number of equality atoms :   28 ( 229 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(t45_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
               => ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A )
                   => ( ( D = E )
                      | ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B )
                        & ( ( k1_funct_1 @ C @ D )
                         != ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( r3_wellord1 @ A @ B @ C )
                 => ! [D: $i,E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A )
                     => ( ( D = E )
                        | ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B )
                          & ( ( k1_funct_1 @ C @ D )
                           != ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_wellord1])).

thf('0',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_1 @ sk_E_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_relat_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
              <=> ( ! [D: $i,E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A )
                    <=> ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B )
                        & ( r2_hidden @ E @ ( k3_relat_1 @ A ) )
                        & ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) ) )
                  & ( v2_funct_1 @ C )
                  & ( ( k2_relat_1 @ C )
                    = ( k3_relat_1 @ B ) )
                  & ( ( k1_relat_1 @ C )
                    = ( k3_relat_1 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
        & ( r2_hidden @ E @ ( k3_relat_1 @ A ) )
        & ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( r3_wellord1 @ A @ B @ C )
              <=> ( ( ( k1_relat_1 @ C )
                    = ( k3_relat_1 @ A ) )
                  & ( ( k2_relat_1 @ C )
                    = ( k3_relat_1 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ! [D: $i,E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A )
                    <=> ( zip_tseitin_0 @ E @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r3_wellord1 @ X9 @ X8 @ X10 )
      | ( zip_tseitin_0 @ X11 @ X12 @ X10 @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X11 ) @ X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A )
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
      | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
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

thf('10',plain,(
    zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X2 @ ( k3_relat_1 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X2 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    r2_hidden @ sk_D_1 @ ( k3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r3_wellord1 @ X9 @ X8 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k3_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( X1
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ X0 ) ) )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r3_wellord1 @ X9 @ X8 @ X10 )
      | ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','32'])).

thf('34',plain,
    ( sk_D_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','33'])).

thf('35',plain,(
    zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_relat_1 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X2 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    r2_hidden @ sk_E_1 @ ( k3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','32'])).

thf('39',plain,
    ( sk_E_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_D_1 ) @ ( k1_funct_1 @ sk_C @ sk_E_1 ) ) @ sk_B )
    | ( ( k1_funct_1 @ sk_C @ sk_D_1 )
      = ( k1_funct_1 @ sk_C @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_D_1 )
      = ( k1_funct_1 @ sk_C @ sk_E_1 ) )
   <= ( ( k1_funct_1 @ sk_C @ sk_D_1 )
      = ( k1_funct_1 @ sk_C @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,(
    zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X5 @ X2 ) @ ( k1_funct_1 @ X5 @ X4 ) ) @ X6 )
      | ~ ( zip_tseitin_0 @ X4 @ X2 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_D_1 ) @ ( k1_funct_1 @ sk_C @ sk_E_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_D_1 ) @ ( k1_funct_1 @ sk_C @ sk_E_1 ) ) @ sk_B )
   <= ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_D_1 ) @ ( k1_funct_1 @ sk_C @ sk_E_1 ) ) @ sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf('46',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_D_1 ) @ ( k1_funct_1 @ sk_C @ sk_E_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_D_1 )
      = ( k1_funct_1 @ sk_C @ sk_E_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_D_1 ) @ ( k1_funct_1 @ sk_C @ sk_E_1 ) ) @ sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_C @ sk_D_1 )
    = ( k1_funct_1 @ sk_C @ sk_E_1 ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_funct_1 @ sk_C @ sk_D_1 )
    = ( k1_funct_1 @ sk_C @ sk_E_1 ) ),
    inference(simpl_trail,[status(thm)],['41','48'])).

thf('50',plain,
    ( sk_E_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['39','49'])).

thf('51',plain,(
    sk_E_1 = sk_D_1 ),
    inference('sup+',[status(thm)],['34','50'])).

thf('52',plain,(
    sk_D_1 != sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PQm1XtGroh
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:46:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 36 iterations in 0.025s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.20/0.47  thf(t45_wellord1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ B ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47               ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.20/0.47                 ( ![D:$i,E:$i]:
% 0.20/0.47                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) =>
% 0.20/0.47                     ( ( ( D ) = ( E ) ) | 
% 0.20/0.47                       ( ( r2_hidden @
% 0.20/0.47                           ( k4_tarski @
% 0.20/0.47                             ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.20/0.47                           B ) & 
% 0.20/0.47                         ( ( k1_funct_1 @ C @ D ) != ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( v1_relat_1 @ A ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( v1_relat_1 @ B ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47                  ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.20/0.47                    ( ![D:$i,E:$i]:
% 0.20/0.47                      ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) =>
% 0.20/0.47                        ( ( ( D ) = ( E ) ) | 
% 0.20/0.47                          ( ( r2_hidden @
% 0.20/0.47                              ( k4_tarski @
% 0.20/0.47                                ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.20/0.47                              B ) & 
% 0.20/0.47                            ( ( k1_funct_1 @ C @ D ) != ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t45_wellord1])).
% 0.20/0.47  thf('0', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r2_hidden @ (k4_tarski @ sk_D_1 @ sk_E_1) @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d7_wellord1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ B ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.20/0.47               ( ( r3_wellord1 @ A @ B @ C ) <=>
% 0.20/0.47                 ( ( ![D:$i,E:$i]:
% 0.20/0.47                     ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) <=>
% 0.20/0.47                       ( ( r2_hidden @
% 0.20/0.47                           ( k4_tarski @
% 0.20/0.47                             ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.20/0.47                           B ) & 
% 0.20/0.47                         ( r2_hidden @ E @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.47                         ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) ) ) ) & 
% 0.20/0.47                   ( v2_funct_1 @ C ) & 
% 0.20/0.47                   ( ( k2_relat_1 @ C ) = ( k3_relat_1 @ B ) ) & 
% 0.20/0.47                   ( ( k1_relat_1 @ C ) = ( k3_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_2, axiom,
% 0.20/0.47    (![E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_0 @ E @ D @ C @ B @ A ) <=>
% 0.20/0.47       ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.47         ( r2_hidden @ E @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.47         ( r2_hidden @
% 0.20/0.47           ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B ) ) ))).
% 0.20/0.47  thf(zf_stmt_3, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ B ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47               ( ( r3_wellord1 @ A @ B @ C ) <=>
% 0.20/0.47                 ( ( ( k1_relat_1 @ C ) = ( k3_relat_1 @ A ) ) & 
% 0.20/0.47                   ( ( k2_relat_1 @ C ) = ( k3_relat_1 @ B ) ) & 
% 0.20/0.47                   ( v2_funct_1 @ C ) & 
% 0.20/0.47                   ( ![D:$i,E:$i]:
% 0.20/0.47                     ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) <=>
% 0.20/0.47                       ( zip_tseitin_0 @ E @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X8)
% 0.20/0.47          | ~ (r3_wellord1 @ X9 @ X8 @ X10)
% 0.20/0.47          | (zip_tseitin_0 @ X11 @ X12 @ X10 @ X8 @ X9)
% 0.20/0.47          | ~ (r2_hidden @ (k4_tarski @ X12 @ X11) @ X9)
% 0.20/0.47          | ~ (v1_funct_1 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ sk_A)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A)
% 0.20/0.47          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A)
% 0.20/0.47          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.47  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain, ((zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((r2_hidden @ X2 @ (k3_relat_1 @ X3))
% 0.20/0.47          | ~ (zip_tseitin_0 @ X4 @ X2 @ X5 @ X6 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.47  thf('12', plain, ((r2_hidden @ sk_D_1 @ (k3_relat_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X8)
% 0.20/0.47          | ~ (r3_wellord1 @ X9 @ X8 @ X10)
% 0.20/0.47          | ((k1_relat_1 @ X10) = (k3_relat_1 @ X9))
% 0.20/0.47          | ~ (v1_funct_1 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47        | ((k1_relat_1 @ sk_C) = (k3_relat_1 @ sk_A))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, (((k1_relat_1 @ sk_C) = (k3_relat_1 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.20/0.47  thf(t56_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.47         ( ( ( A ) =
% 0.20/0.47             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.20/0.47           ( ( A ) =
% 0.20/0.47             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v2_funct_1 @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.47          | ((X1) = (k1_funct_1 @ (k2_funct_1 @ X0) @ (k1_funct_1 @ X0 @ X1)))
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.20/0.47          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47          | ((X0)
% 0.20/0.47              = (k1_funct_1 @ (k2_funct_1 @ sk_C) @ (k1_funct_1 @ sk_C @ X0)))
% 0.20/0.47          | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X8)
% 0.20/0.47          | ~ (r3_wellord1 @ X9 @ X8 @ X10)
% 0.20/0.47          | (v2_funct_1 @ X10)
% 0.20/0.47          | ~ (v1_funct_1 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47        | (v2_funct_1 @ sk_C)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.20/0.47          | ((X0)
% 0.20/0.47              = (k1_funct_1 @ (k2_funct_1 @ sk_C) @ (k1_funct_1 @ sk_C @ X0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23', '24', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (((sk_D_1)
% 0.20/0.47         = (k1_funct_1 @ (k2_funct_1 @ sk_C) @ (k1_funct_1 @ sk_C @ sk_D_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '33'])).
% 0.20/0.47  thf('35', plain, ((zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((r2_hidden @ X4 @ (k3_relat_1 @ X3))
% 0.20/0.47          | ~ (zip_tseitin_0 @ X4 @ X2 @ X5 @ X6 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.47  thf('37', plain, ((r2_hidden @ sk_E_1 @ (k3_relat_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.20/0.47          | ((X0)
% 0.20/0.47              = (k1_funct_1 @ (k2_funct_1 @ sk_C) @ (k1_funct_1 @ sk_C @ X0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23', '24', '32'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((sk_E_1)
% 0.20/0.47         = (k1_funct_1 @ (k2_funct_1 @ sk_C) @ (k1_funct_1 @ sk_C @ sk_E_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      ((~ (r2_hidden @ 
% 0.20/0.47           (k4_tarski @ (k1_funct_1 @ sk_C @ sk_D_1) @ 
% 0.20/0.47            (k1_funct_1 @ sk_C @ sk_E_1)) @ 
% 0.20/0.47           sk_B)
% 0.20/0.47        | ((k1_funct_1 @ sk_C @ sk_D_1) = (k1_funct_1 @ sk_C @ sk_E_1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_C @ sk_D_1) = (k1_funct_1 @ sk_C @ sk_E_1)))
% 0.20/0.47         <= ((((k1_funct_1 @ sk_C @ sk_D_1) = (k1_funct_1 @ sk_C @ sk_E_1))))),
% 0.20/0.47      inference('split', [status(esa)], ['40'])).
% 0.20/0.47  thf('42', plain, ((zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((r2_hidden @ 
% 0.20/0.47           (k4_tarski @ (k1_funct_1 @ X5 @ X2) @ (k1_funct_1 @ X5 @ X4)) @ X6)
% 0.20/0.47          | ~ (zip_tseitin_0 @ X4 @ X2 @ X5 @ X6 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      ((r2_hidden @ 
% 0.20/0.47        (k4_tarski @ (k1_funct_1 @ sk_C @ sk_D_1) @ 
% 0.20/0.47         (k1_funct_1 @ sk_C @ sk_E_1)) @ 
% 0.20/0.47        sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      ((~ (r2_hidden @ 
% 0.20/0.47           (k4_tarski @ (k1_funct_1 @ sk_C @ sk_D_1) @ 
% 0.20/0.47            (k1_funct_1 @ sk_C @ sk_E_1)) @ 
% 0.20/0.47           sk_B))
% 0.20/0.47         <= (~
% 0.20/0.47             ((r2_hidden @ 
% 0.20/0.47               (k4_tarski @ (k1_funct_1 @ sk_C @ sk_D_1) @ 
% 0.20/0.47                (k1_funct_1 @ sk_C @ sk_E_1)) @ 
% 0.20/0.47               sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['40'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (((r2_hidden @ 
% 0.20/0.47         (k4_tarski @ (k1_funct_1 @ sk_C @ sk_D_1) @ 
% 0.20/0.47          (k1_funct_1 @ sk_C @ sk_E_1)) @ 
% 0.20/0.47         sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_C @ sk_D_1) = (k1_funct_1 @ sk_C @ sk_E_1))) | 
% 0.20/0.47       ~
% 0.20/0.47       ((r2_hidden @ 
% 0.20/0.47         (k4_tarski @ (k1_funct_1 @ sk_C @ sk_D_1) @ 
% 0.20/0.47          (k1_funct_1 @ sk_C @ sk_E_1)) @ 
% 0.20/0.47         sk_B))),
% 0.20/0.47      inference('split', [status(esa)], ['40'])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_C @ sk_D_1) = (k1_funct_1 @ sk_C @ sk_E_1)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (((k1_funct_1 @ sk_C @ sk_D_1) = (k1_funct_1 @ sk_C @ sk_E_1))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['41', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      (((sk_E_1)
% 0.20/0.47         = (k1_funct_1 @ (k2_funct_1 @ sk_C) @ (k1_funct_1 @ sk_C @ sk_D_1)))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '49'])).
% 0.20/0.47  thf('51', plain, (((sk_E_1) = (sk_D_1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['34', '50'])).
% 0.20/0.47  thf('52', plain, (((sk_D_1) != (sk_E_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('53', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
