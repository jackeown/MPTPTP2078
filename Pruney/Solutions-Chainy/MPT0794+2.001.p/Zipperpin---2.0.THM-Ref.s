%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hpkuo7TRHK

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 309 expanded)
%              Number of leaves         :   35 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          : 1042 (5805 expanded)
%              Number of equality atoms :   67 ( 328 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B )
   <= ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('4',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_1 @ sk_E_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ ( k3_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ sk_E_1 @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_E_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C_1 ),
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

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( r3_wellord1 @ X27 @ X26 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k3_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ ( k1_tarski @ X18 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_E_1 ) ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_E_1 ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['3','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_E_1 ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_E_1 ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_1 @ sk_E_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X13 @ ( k3_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ sk_D_1 @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ sk_D_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('34',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_E_1 ) ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,(
    r2_hidden @ sk_E_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X8 ) @ X10 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_E_1 ) @ ( k3_relat_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_E_1 ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_tarski @ sk_E_1 ) @ ( k3_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( r3_wellord1 @ X27 @ X26 @ X28 )
      | ( v2_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49','57'])).

thf('59',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_E_1 ) ) )
    = ( k1_tarski @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['44','58'])).

thf('60',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) ) )
      = ( k1_tarski @ sk_E_1 ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['38','59'])).

thf('61',plain,(
    r2_hidden @ sk_D_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('62',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X8 ) @ X10 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('63',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_relat_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_D_1 ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ ( k3_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49','57'])).

thf('68',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_tarski @ sk_E_1 )
      = ( k1_tarski @ sk_D_1 ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['60','68'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('71',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_E_1 @ ( k1_tarski @ sk_D_1 ) )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('74',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_E_1 = sk_D_1 )
   <= ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    sk_D_1 != sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
 != ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B )
    | ( ( k1_funct_1 @ sk_C_1 @ sk_D_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','79'])).

thf('81',plain,(
    r3_wellord1 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r2_hidden @ ( k4_tarski @ sk_D_1 @ sk_E_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( r3_wellord1 @ X27 @ X26 @ X28 )
      | ( zip_tseitin_0 @ X29 @ X30 @ X28 @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ X29 ) @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A )
      | ~ ( r3_wellord1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X23 @ X20 ) @ ( k1_funct_1 @ X23 @ X22 ) ) @ X24 )
      | ~ ( zip_tseitin_0 @ X22 @ X20 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('93',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_D_1 ) @ ( k1_funct_1 @ sk_C_1 @ sk_E_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['80','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hpkuo7TRHK
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 157 iterations in 0.091s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.38/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.38/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.55  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.55  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.38/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.55  thf(t45_wellord1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( v1_relat_1 @ B ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.55               ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.38/0.55                 ( ![D:$i,E:$i]:
% 0.38/0.55                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) =>
% 0.38/0.55                     ( ( ( D ) = ( E ) ) | 
% 0.38/0.55                       ( ( r2_hidden @
% 0.38/0.55                           ( k4_tarski @
% 0.38/0.55                             ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.38/0.55                           B ) & 
% 0.38/0.55                         ( ( k1_funct_1 @ C @ D ) != ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( v1_relat_1 @ A ) =>
% 0.38/0.55          ( ![B:$i]:
% 0.38/0.55            ( ( v1_relat_1 @ B ) =>
% 0.38/0.55              ( ![C:$i]:
% 0.38/0.55                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.55                  ( ( r3_wellord1 @ A @ B @ C ) =>
% 0.38/0.55                    ( ![D:$i,E:$i]:
% 0.38/0.55                      ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) =>
% 0.38/0.55                        ( ( ( D ) = ( E ) ) | 
% 0.38/0.55                          ( ( r2_hidden @
% 0.38/0.55                              ( k4_tarski @
% 0.38/0.55                                ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.38/0.55                              B ) & 
% 0.38/0.55                            ( ( k1_funct_1 @ C @ D ) != ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t45_wellord1])).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      ((~ (r2_hidden @ 
% 0.38/0.55           (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.38/0.55            (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.38/0.55           sk_B)
% 0.38/0.55        | ((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      ((~ (r2_hidden @ 
% 0.38/0.55           (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.38/0.55            (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.38/0.55           sk_B))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ 
% 0.38/0.55               (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.38/0.55                (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.38/0.55               sk_B)))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1)))
% 0.38/0.55         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf(t148_relat_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ B ) =>
% 0.38/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.38/0.55          | ~ (v1_relat_1 @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.55  thf('4', plain, ((r2_hidden @ (k4_tarski @ sk_D_1 @ sk_E_1) @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t30_relat_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ C ) =>
% 0.38/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.38/0.55         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.38/0.55           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.55         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.38/0.55          | (r2_hidden @ X14 @ (k3_relat_1 @ X15))
% 0.38/0.55          | ~ (v1_relat_1 @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      ((~ (v1_relat_1 @ sk_A) | (r2_hidden @ sk_E_1 @ (k3_relat_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('8', plain, ((r2_hidden @ sk_E_1 @ (k3_relat_1 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf('9', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d7_wellord1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( v1_relat_1 @ B ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.38/0.55               ( ( r3_wellord1 @ A @ B @ C ) <=>
% 0.38/0.55                 ( ( ![D:$i,E:$i]:
% 0.38/0.55                     ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) <=>
% 0.38/0.55                       ( ( r2_hidden @
% 0.38/0.55                           ( k4_tarski @
% 0.38/0.55                             ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.38/0.55                           B ) & 
% 0.38/0.55                         ( r2_hidden @ E @ ( k3_relat_1 @ A ) ) & 
% 0.38/0.55                         ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) ) ) ) & 
% 0.38/0.55                   ( v2_funct_1 @ C ) & 
% 0.38/0.55                   ( ( k2_relat_1 @ C ) = ( k3_relat_1 @ B ) ) & 
% 0.38/0.55                   ( ( k1_relat_1 @ C ) = ( k3_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.38/0.55  thf(zf_stmt_2, axiom,
% 0.38/0.55    (![E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.55     ( ( zip_tseitin_0 @ E @ D @ C @ B @ A ) <=>
% 0.38/0.55       ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.38/0.55         ( r2_hidden @ E @ ( k3_relat_1 @ A ) ) & 
% 0.38/0.55         ( r2_hidden @
% 0.38/0.55           ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B ) ) ))).
% 0.38/0.55  thf(zf_stmt_3, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( v1_relat_1 @ B ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.55               ( ( r3_wellord1 @ A @ B @ C ) <=>
% 0.38/0.55                 ( ( ( k1_relat_1 @ C ) = ( k3_relat_1 @ A ) ) & 
% 0.38/0.55                   ( ( k2_relat_1 @ C ) = ( k3_relat_1 @ B ) ) & 
% 0.38/0.55                   ( v2_funct_1 @ C ) & 
% 0.38/0.55                   ( ![D:$i,E:$i]:
% 0.38/0.55                     ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) <=>
% 0.38/0.55                       ( zip_tseitin_0 @ E @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X26)
% 0.38/0.55          | ~ (r3_wellord1 @ X27 @ X26 @ X28)
% 0.38/0.55          | ((k1_relat_1 @ X28) = (k3_relat_1 @ X27))
% 0.38/0.55          | ~ (v1_funct_1 @ X28)
% 0.38/0.55          | ~ (v1_relat_1 @ X28)
% 0.38/0.55          | ~ (v1_relat_1 @ X27))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.55        | ((k1_relat_1 @ sk_C_1) = (k3_relat_1 @ sk_A))
% 0.38/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('16', plain, (((k1_relat_1 @ sk_C_1) = (k3_relat_1 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.38/0.55  thf(t168_funct_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.55       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.55         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.38/0.55           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      (![X18 : $i, X19 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.38/0.55          | ((k2_relat_1 @ (k7_relat_1 @ X19 @ (k1_tarski @ X18)))
% 0.38/0.55              = (k1_tarski @ (k1_funct_1 @ X19 @ X18)))
% 0.38/0.55          | ~ (v1_funct_1 @ X19)
% 0.38/0.55          | ~ (v1_relat_1 @ X19))),
% 0.38/0.55      inference('cnf', [status(esa)], [t168_funct_1])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.38/0.55          | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.55          | ((k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_tarski @ X0)))
% 0.38/0.55              = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.55  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.38/0.55          | ((k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_tarski @ X0)))
% 0.38/0.55              = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 0.38/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (((k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_E_1)))
% 0.38/0.55         = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_E_1)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['8', '21'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      ((((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_E_1))
% 0.38/0.55          = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_E_1)))
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['3', '22'])).
% 0.38/0.55  thf('24', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_E_1))
% 0.38/0.55         = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_E_1)))),
% 0.38/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      ((((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_E_1))
% 0.38/0.55          = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1))))
% 0.38/0.55         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['2', '25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]:
% 0.38/0.55         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.38/0.55          | ~ (v1_relat_1 @ X11))),
% 0.38/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.55  thf('28', plain, ((r2_hidden @ (k4_tarski @ sk_D_1 @ sk_E_1) @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.55         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.38/0.55          | (r2_hidden @ X13 @ (k3_relat_1 @ X15))
% 0.38/0.55          | ~ (v1_relat_1 @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      ((~ (v1_relat_1 @ sk_A) | (r2_hidden @ sk_D_1 @ (k3_relat_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.55  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('32', plain, ((r2_hidden @ sk_D_1 @ (k3_relat_1 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_A))
% 0.38/0.55          | ((k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_tarski @ X0)))
% 0.38/0.55              = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 0.38/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (((k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D_1)))
% 0.38/0.55         = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      ((((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D_1))
% 0.38/0.55          = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1)))
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['27', '34'])).
% 0.38/0.55  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D_1))
% 0.38/0.55         = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      ((((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D_1))
% 0.38/0.55          = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_E_1))))
% 0.38/0.55         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['26', '37'])).
% 0.38/0.55  thf('39', plain, ((r2_hidden @ sk_E_1 @ (k3_relat_1 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf(l35_zfmisc_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.55       ( r2_hidden @ A @ B ) ))).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (![X8 : $i, X10 : $i]:
% 0.38/0.55         (((k4_xboole_0 @ (k1_tarski @ X8) @ X10) = (k1_xboole_0))
% 0.38/0.55          | ~ (r2_hidden @ X8 @ X10))),
% 0.38/0.55      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_E_1) @ (k3_relat_1 @ sk_A))
% 0.38/0.55         = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.55  thf(t37_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.55        | (r1_tarski @ (k1_tarski @ sk_E_1) @ (k3_relat_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.55  thf('44', plain, ((r1_tarski @ (k1_tarski @ sk_E_1) @ (k3_relat_1 @ sk_A))),
% 0.38/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.55  thf('45', plain, (((k1_relat_1 @ sk_C_1) = (k3_relat_1 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 0.38/0.55  thf(t164_funct_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.55       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.38/0.55         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.38/0.55  thf('46', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.38/0.55          | ~ (v2_funct_1 @ X17)
% 0.38/0.55          | ((k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X16)) = (X16))
% 0.38/0.55          | ~ (v1_funct_1 @ X17)
% 0.38/0.55          | ~ (v1_relat_1 @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_A))
% 0.38/0.55          | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.55          | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ X0)) = (X0))
% 0.38/0.55          | ~ (v2_funct_1 @ sk_C_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.55  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('49', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('50', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X26)
% 0.38/0.55          | ~ (r3_wellord1 @ X27 @ X26 @ X28)
% 0.38/0.55          | (v2_funct_1 @ X28)
% 0.38/0.55          | ~ (v1_funct_1 @ X28)
% 0.38/0.55          | ~ (v1_relat_1 @ X28)
% 0.38/0.55          | ~ (v1_relat_1 @ X27))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      ((~ (v1_relat_1 @ sk_A)
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.55        | (v2_funct_1 @ sk_C_1)
% 0.38/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.55  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('57', plain, ((v2_funct_1 @ sk_C_1)),
% 0.38/0.55      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_A))
% 0.38/0.55          | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['47', '48', '49', '57'])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      (((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_E_1)))
% 0.38/0.55         = (k1_tarski @ sk_E_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['44', '58'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      ((((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D_1)))
% 0.38/0.55          = (k1_tarski @ sk_E_1)))
% 0.38/0.55         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['38', '59'])).
% 0.38/0.55  thf('61', plain, ((r2_hidden @ sk_D_1 @ (k3_relat_1 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      (![X8 : $i, X10 : $i]:
% 0.38/0.55         (((k4_xboole_0 @ (k1_tarski @ X8) @ X10) = (k1_xboole_0))
% 0.38/0.55          | ~ (r2_hidden @ X8 @ X10))),
% 0.38/0.55      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.38/0.55  thf('63', plain,
% 0.38/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_relat_1 @ sk_A))
% 0.38/0.55         = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.55  thf('64', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.55        | (r1_tarski @ (k1_tarski @ sk_D_1) @ (k3_relat_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.55  thf('66', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ (k3_relat_1 @ sk_A))),
% 0.38/0.55      inference('simplify', [status(thm)], ['65'])).
% 0.38/0.55  thf('67', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_A))
% 0.38/0.55          | ((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 0.38/0.55      inference('demod', [status(thm)], ['47', '48', '49', '57'])).
% 0.38/0.55  thf('68', plain,
% 0.38/0.55      (((k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_D_1)))
% 0.38/0.55         = (k1_tarski @ sk_D_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.55  thf('69', plain,
% 0.38/0.55      ((((k1_tarski @ sk_E_1) = (k1_tarski @ sk_D_1)))
% 0.38/0.55         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['60', '68'])).
% 0.38/0.55  thf(d1_tarski, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.55  thf('70', plain,
% 0.38/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.55         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.55  thf('71', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.38/0.55      inference('simplify', [status(thm)], ['70'])).
% 0.38/0.55  thf('72', plain,
% 0.38/0.55      (((r2_hidden @ sk_E_1 @ (k1_tarski @ sk_D_1)))
% 0.38/0.55         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['69', '71'])).
% 0.38/0.55  thf('73', plain,
% 0.38/0.55      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.55  thf('74', plain,
% 0.38/0.55      (![X3 : $i, X6 : $i]:
% 0.38/0.55         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.38/0.55  thf('75', plain,
% 0.38/0.55      ((((sk_E_1) = (sk_D_1)))
% 0.38/0.55         <= ((((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['72', '74'])).
% 0.38/0.55  thf('76', plain, (((sk_D_1) != (sk_E_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('77', plain,
% 0.38/0.55      (~ (((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1)))),
% 0.38/0.55      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.38/0.55  thf('78', plain,
% 0.38/0.55      (~
% 0.38/0.55       ((r2_hidden @ 
% 0.38/0.55         (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.38/0.55          (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.38/0.55         sk_B)) | 
% 0.38/0.55       (((k1_funct_1 @ sk_C_1 @ sk_D_1) = (k1_funct_1 @ sk_C_1 @ sk_E_1)))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('79', plain,
% 0.38/0.55      (~
% 0.38/0.55       ((r2_hidden @ 
% 0.38/0.55         (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.38/0.55          (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.38/0.55         sk_B))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.38/0.55  thf('80', plain,
% 0.38/0.55      (~ (r2_hidden @ 
% 0.38/0.55          (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.38/0.55           (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.38/0.55          sk_B)),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['1', '79'])).
% 0.38/0.55  thf('81', plain, ((r3_wellord1 @ sk_A @ sk_B @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('82', plain, ((r2_hidden @ (k4_tarski @ sk_D_1 @ sk_E_1) @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('83', plain,
% 0.38/0.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X26)
% 0.38/0.55          | ~ (r3_wellord1 @ X27 @ X26 @ X28)
% 0.38/0.55          | (zip_tseitin_0 @ X29 @ X30 @ X28 @ X26 @ X27)
% 0.38/0.55          | ~ (r2_hidden @ (k4_tarski @ X30 @ X29) @ X27)
% 0.38/0.55          | ~ (v1_funct_1 @ X28)
% 0.38/0.55          | ~ (v1_relat_1 @ X28)
% 0.38/0.55          | ~ (v1_relat_1 @ X27))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.55  thf('84', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ sk_A)
% 0.38/0.55          | ~ (v1_relat_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A)
% 0.38/0.55          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.38/0.55          | ~ (v1_relat_1 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.38/0.55  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('86', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ X0 @ X1 @ sk_A)
% 0.38/0.55          | ~ (r3_wellord1 @ sk_A @ X1 @ X0)
% 0.38/0.55          | ~ (v1_relat_1 @ X1))),
% 0.38/0.55      inference('demod', [status(thm)], ['84', '85'])).
% 0.38/0.55  thf('87', plain,
% 0.38/0.55      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.55        | (zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.55        | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['81', '86'])).
% 0.38/0.55  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('89', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('90', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('91', plain, ((zip_tseitin_0 @ sk_E_1 @ sk_D_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.55      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.38/0.55  thf('92', plain,
% 0.38/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.55         ((r2_hidden @ 
% 0.38/0.55           (k4_tarski @ (k1_funct_1 @ X23 @ X20) @ (k1_funct_1 @ X23 @ X22)) @ 
% 0.38/0.55           X24)
% 0.38/0.55          | ~ (zip_tseitin_0 @ X22 @ X20 @ X23 @ X24 @ X21))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.55  thf('93', plain,
% 0.38/0.55      ((r2_hidden @ 
% 0.38/0.55        (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_D_1) @ 
% 0.38/0.55         (k1_funct_1 @ sk_C_1 @ sk_E_1)) @ 
% 0.38/0.55        sk_B)),
% 0.38/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.38/0.55  thf('94', plain, ($false), inference('demod', [status(thm)], ['80', '93'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
