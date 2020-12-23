%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RUrAPuMFpY

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 189 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  670 (3873 expanded)
%              Number of equality atoms :   36 ( 202 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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

thf('0',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B_1 )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r3_wellord1 @ sk_A @ sk_B_1 @ sk_C_1 ),
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

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r3_wellord1 @ X10 @ X9 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k3_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
       != ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('15',plain,(
    r3_wellord1 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r3_wellord1 @ X10 @ X9 @ X11 )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_C_1 @ X0 )
       != ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
        | ( sk_E_1 = X0 )
        | ~ ( r2_hidden @ sk_E_1 @ ( k3_relat_1 @ sk_A ) ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    r3_wellord1 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_1 @ sk_E_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r3_wellord1 @ X10 @ X9 @ X11 )
      | ( zip_tseitin_0 @ X12 @ X13 @ X11 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X12 ) @ X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A )
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
      | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k3_relat_1 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X3 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    r2_hidden @ sk_E_1 @ ( k3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
         != ( k1_funct_1 @ sk_C_1 @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
        | ( sk_E_1 = X0 ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['24','37'])).

thf('39',plain,(
    zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X6 @ X3 ) @ ( k1_funct_1 @ X6 @ X5 ) ) @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X3 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
    = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( sk_E_1 = X0 ) ) ),
    inference(simpl_trail,[status(thm)],['38','45'])).

thf('47',plain,
    ( ( sk_E_1 = sk_D_1 )
    | ~ ( r2_hidden @ sk_D_1 @ ( k3_relat_1 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,(
    zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X3 @ ( k3_relat_1 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X3 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('50',plain,(
    r2_hidden @ sk_D_1 @ ( k3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_E_1 = sk_D_1 ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    sk_D_1 != sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RUrAPuMFpY
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 44 iterations in 0.029s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.48  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.48  thf(t45_wellord1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48               ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.20/0.48                 ( ![D:$i,E:$i]:
% 0.20/0.48                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) =>
% 0.20/0.48                     ( ( ( D ) = ( E ) ) | 
% 0.20/0.48                       ( ( r2_hidden @
% 0.20/0.48                           ( k4_tarski @
% 0.20/0.48                             ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.20/0.48                           B ) & 
% 0.20/0.48                         ( ( k1_funct_1 @ C @ D ) != ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( v1_relat_1 @ B ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48                  ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.20/0.48                    ( ![D:$i,E:$i]:
% 0.20/0.48                      ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) =>
% 0.20/0.48                        ( ( ( D ) = ( E ) ) | 
% 0.20/0.48                          ( ( r2_hidden @
% 0.20/0.48                              ( k4_tarski @
% 0.20/0.48                                ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.20/0.48                              B ) & 
% 0.20/0.48                            ( ( k1_funct_1 @ C @ D ) != ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t45_wellord1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (r2_hidden @ 
% 0.20/0.48           (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.20/0.48            (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.20/0.48           sk_B_1)
% 0.20/0.48        | ((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1)))
% 0.20/0.48         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain, ((r3_wellord1 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d7_wellord1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.20/0.48               ( ( r3_wellord1 @ A @ B @ C ) <=>
% 0.20/0.48                 ( ( ![D:$i,E:$i]:
% 0.20/0.48                     ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) <=>
% 0.20/0.48                       ( ( r2_hidden @
% 0.20/0.48                           ( k4_tarski @
% 0.20/0.48                             ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.20/0.48                           B ) & 
% 0.20/0.48                         ( r2_hidden @ E @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.48                         ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) ) ) ) & 
% 0.20/0.48                   ( v2_funct_1 @ C ) & 
% 0.20/0.48                   ( ( k2_relat_1 @ C ) = ( k3_relat_1 @ B ) ) & 
% 0.20/0.48                   ( ( k1_relat_1 @ C ) = ( k3_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_2, axiom,
% 0.20/0.48    (![E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_0 @ E @ D @ C @ B @ A ) <=>
% 0.20/0.48       ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.48         ( r2_hidden @ E @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.48         ( r2_hidden @
% 0.20/0.48           ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B ) ) ))).
% 0.20/0.48  thf(zf_stmt_3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48               ( ( r3_wellord1 @ A @ B @ C ) <=>
% 0.20/0.48                 ( ( ( k1_relat_1 @ C ) = ( k3_relat_1 @ A ) ) & 
% 0.20/0.48                   ( ( k2_relat_1 @ C ) = ( k3_relat_1 @ B ) ) & 
% 0.20/0.48                   ( v2_funct_1 @ C ) & 
% 0.20/0.48                   ( ![D:$i,E:$i]:
% 0.20/0.48                     ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) <=>
% 0.20/0.48                       ( zip_tseitin_0 @ E @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X9)
% 0.20/0.48          | ~ (r3_wellord1 @ X10 @ X9 @ X11)
% 0.20/0.48          | ((k1_relat_1 @ X11) = (k3_relat_1 @ X10))
% 0.20/0.48          | ~ (v1_funct_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.48        | ((k1_relat_1 @ sk_C_1) = (k3_relat_1 @ sk_A))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain, (((k1_relat_1 @ sk_C_1) = (k3_relat_1 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.48  thf(d8_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.48         ( ![B:$i,C:$i]:
% 0.20/0.48           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.48               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.48               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.48             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (v2_funct_1 @ X0)
% 0.20/0.48          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.20/0.48          | ((k1_funct_1 @ X0 @ X1) != (k1_funct_1 @ X0 @ X2))
% 0.20/0.48          | ((X1) = (X2))
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.20/0.48          | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.48          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.48          | ((X0) = (X1))
% 0.20/0.48          | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 0.20/0.48          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_1))
% 0.20/0.48          | ~ (v2_funct_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, (((k1_relat_1 @ sk_C_1) = (k3_relat_1 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.48  thf('15', plain, ((r3_wellord1 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X9)
% 0.20/0.48          | ~ (r3_wellord1 @ X10 @ X9 @ X11)
% 0.20/0.48          | (v2_funct_1 @ X11)
% 0.20/0.48          | ~ (v1_funct_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.48        | (v2_funct_1 @ sk_C_1)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, ((v2_funct_1 @ sk_C_1)),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.20/0.48          | ((X0) = (X1))
% 0.20/0.48          | ((k1_funct_1 @ sk_C_1 @ X0) != (k1_funct_1 @ sk_C_1 @ X1))
% 0.20/0.48          | ~ (r2_hidden @ X1 @ (k3_relat_1 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12', '13', '14', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (((k1_funct_1 @ sk_C_1 @ sk_D_1) != (k1_funct_1 @ sk_C_1 @ X0))
% 0.20/0.48           | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.20/0.48           | ((sk_E_1) = (X0))
% 0.20/0.48           | ~ (r2_hidden @ sk_E_1 @ (k3_relat_1 @ sk_A))))
% 0.20/0.48         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '23'])).
% 0.20/0.48  thf('25', plain, ((r3_wellord1 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain, ((r2_hidden @ (k4_tarski @ sk_D_1 @ sk_E_1) @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X9)
% 0.20/0.48          | ~ (r3_wellord1 @ X10 @ X9 @ X11)
% 0.20/0.48          | (zip_tseitin_0 @ X12 @ X13 @ X11 @ X9 @ X10)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X13 @ X12) @ X10)
% 0.20/0.48          | ~ (v1_funct_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ sk_A)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A)
% 0.20/0.48          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A)
% 0.20/0.48          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.48        | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '30'])).
% 0.20/0.48  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((r2_hidden @ X5 @ (k3_relat_1 @ X4))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X5 @ X3 @ X6 @ X7 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.48  thf('37', plain, ((r2_hidden @ sk_E_1 @ (k3_relat_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (((k1_funct_1 @ sk_C_1 @ sk_D_1) != (k1_funct_1 @ sk_C_1 @ X0))
% 0.20/0.48           | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.20/0.48           | ((sk_E_1) = (X0))))
% 0.20/0.48         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((r2_hidden @ 
% 0.20/0.48           (k4_tarski @ (k1_funct_1 @ X6 @ X3) @ (k1_funct_1 @ X6 @ X5)) @ X7)
% 0.20/0.48          | ~ (zip_tseitin_0 @ X5 @ X3 @ X6 @ X7 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((r2_hidden @ 
% 0.20/0.48        (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.20/0.48         (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.20/0.48        sk_B_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((~ (r2_hidden @ 
% 0.20/0.48           (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.20/0.48            (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.20/0.48           sk_B_1))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ 
% 0.20/0.48               (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.20/0.48                (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.20/0.48               sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (((r2_hidden @ 
% 0.20/0.48         (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.20/0.48          (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.20/0.48         sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))) | 
% 0.20/0.48       ~
% 0.20/0.48       ((r2_hidden @ 
% 0.20/0.48         (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.20/0.48          (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.20/0.48         sk_B_1))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_funct_1 @ sk_C_1 @ sk_D_1) != (k1_funct_1 @ sk_C_1 @ X0))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.20/0.48          | ((sk_E_1) = (X0)))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['38', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((((sk_E_1) = (sk_D_1)) | ~ (r2_hidden @ sk_D_1 @ (k3_relat_1 @ sk_A)))),
% 0.20/0.48      inference('eq_res', [status(thm)], ['46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         ((r2_hidden @ X3 @ (k3_relat_1 @ X4))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X5 @ X3 @ X6 @ X7 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.48  thf('50', plain, ((r2_hidden @ sk_D_1 @ (k3_relat_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, (((sk_E_1) = (sk_D_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['47', '50'])).
% 0.20/0.48  thf('52', plain, (((sk_D_1) != (sk_E_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('53', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
