%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KelDCLyZFF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:03 EST 2020

% Result     : Theorem 3.46s
% Output     : Refutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  149 (2193 expanded)
%              Number of leaves         :   23 ( 770 expanded)
%              Depth                    :   25
%              Number of atoms          : 1460 (21297 expanded)
%              Number of equality atoms :   95 (1527 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X27 )
        = X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X18 @ X19 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X18 @ X19 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('21',plain,(
    ! [X29: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X29 ) ) @ X29 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k5_relat_1 @ X21 @ ( k5_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('37',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','39'])).

thf('41',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X18 @ X19 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('48',plain,(
    ! [X29: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X29 ) ) @ X29 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('49',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k5_relat_1 @ X21 @ ( k5_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('58',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','59'])).

thf('61',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('63',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('67',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k5_relat_1 @ X21 @ ( k5_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('70',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('75',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('92',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('96',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('101',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['93','109'])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('111',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','114'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('116',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','114'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','122'])).

thf('124',plain,(
    $false ),
    inference(simplify,[status(thm)],['123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KelDCLyZFF
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.46/3.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.46/3.62  % Solved by: fo/fo7.sh
% 3.46/3.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.46/3.62  % done 3011 iterations in 3.168s
% 3.46/3.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.46/3.62  % SZS output start Refutation
% 3.46/3.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.46/3.62  thf(sk_B_type, type, sk_B: $i).
% 3.46/3.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.46/3.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.46/3.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.46/3.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.46/3.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.46/3.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.46/3.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.46/3.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.46/3.62  thf(sk_A_type, type, sk_A: $i).
% 3.46/3.62  thf(t94_relat_1, axiom,
% 3.46/3.62    (![A:$i,B:$i]:
% 3.46/3.62     ( ( v1_relat_1 @ B ) =>
% 3.46/3.62       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 3.46/3.62  thf('0', plain,
% 3.46/3.62      (![X31 : $i, X32 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.46/3.62          | ~ (v1_relat_1 @ X32))),
% 3.46/3.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.46/3.62  thf(t43_funct_1, conjecture,
% 3.46/3.62    (![A:$i,B:$i]:
% 3.46/3.62     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 3.46/3.62       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.46/3.62  thf(zf_stmt_0, negated_conjecture,
% 3.46/3.62    (~( ![A:$i,B:$i]:
% 3.46/3.62        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 3.46/3.62          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 3.46/3.62    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 3.46/3.62  thf('1', plain,
% 3.46/3.62      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 3.46/3.62         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 3.46/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.46/3.62  thf('2', plain,
% 3.46/3.62      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.46/3.62          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 3.46/3.62        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 3.46/3.62      inference('sup-', [status(thm)], ['0', '1'])).
% 3.46/3.62  thf(fc3_funct_1, axiom,
% 3.46/3.62    (![A:$i]:
% 3.46/3.62     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.46/3.62       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.46/3.62  thf('3', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('4', plain,
% 3.46/3.62      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.46/3.62         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 3.46/3.62      inference('demod', [status(thm)], ['2', '3'])).
% 3.46/3.62  thf('5', plain,
% 3.46/3.62      (![X31 : $i, X32 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.46/3.62          | ~ (v1_relat_1 @ X32))),
% 3.46/3.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.46/3.62  thf(t17_xboole_1, axiom,
% 3.46/3.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.46/3.62  thf('6', plain,
% 3.46/3.62      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 3.46/3.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.46/3.62  thf(t71_relat_1, axiom,
% 3.46/3.62    (![A:$i]:
% 3.46/3.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.46/3.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.46/3.62  thf('7', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 3.46/3.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.46/3.62  thf(t77_relat_1, axiom,
% 3.46/3.62    (![A:$i,B:$i]:
% 3.46/3.62     ( ( v1_relat_1 @ B ) =>
% 3.46/3.62       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 3.46/3.62         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 3.46/3.62  thf('8', plain,
% 3.46/3.62      (![X27 : $i, X28 : $i]:
% 3.46/3.62         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 3.46/3.62          | ((k5_relat_1 @ (k6_relat_1 @ X28) @ X27) = (X27))
% 3.46/3.62          | ~ (v1_relat_1 @ X27))),
% 3.46/3.62      inference('cnf', [status(esa)], [t77_relat_1])).
% 3.46/3.62  thf('9', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (~ (r1_tarski @ X0 @ X1)
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.46/3.62          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 3.46/3.62              = (k6_relat_1 @ X0)))),
% 3.46/3.62      inference('sup-', [status(thm)], ['7', '8'])).
% 3.46/3.62  thf('10', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('11', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (~ (r1_tarski @ X0 @ X1)
% 3.46/3.62          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 3.46/3.62              = (k6_relat_1 @ X0)))),
% 3.46/3.62      inference('demod', [status(thm)], ['9', '10'])).
% 3.46/3.62  thf('12', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.46/3.62           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 3.46/3.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.46/3.62      inference('sup-', [status(thm)], ['6', '11'])).
% 3.46/3.62  thf('13', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 3.46/3.62            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 3.46/3.62      inference('sup+', [status(thm)], ['5', '12'])).
% 3.46/3.62  thf('14', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('15', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k7_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 3.46/3.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.46/3.62      inference('demod', [status(thm)], ['13', '14'])).
% 3.46/3.62  thf('16', plain,
% 3.46/3.62      (![X31 : $i, X32 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.46/3.62          | ~ (v1_relat_1 @ X32))),
% 3.46/3.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.46/3.62  thf(t192_relat_1, axiom,
% 3.46/3.62    (![A:$i,B:$i]:
% 3.46/3.62     ( ( v1_relat_1 @ B ) =>
% 3.46/3.62       ( ( k7_relat_1 @ B @ A ) =
% 3.46/3.62         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 3.46/3.62  thf('17', plain,
% 3.46/3.62      (![X18 : $i, X19 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X18 @ X19)
% 3.46/3.62            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19)))
% 3.46/3.62          | ~ (v1_relat_1 @ X18))),
% 3.46/3.62      inference('cnf', [status(esa)], [t192_relat_1])).
% 3.46/3.62  thf('18', plain,
% 3.46/3.62      (![X31 : $i, X32 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.46/3.62          | ~ (v1_relat_1 @ X32))),
% 3.46/3.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.46/3.62  thf('19', plain,
% 3.46/3.62      (![X18 : $i, X19 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X18 @ X19)
% 3.46/3.62            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19)))
% 3.46/3.62          | ~ (v1_relat_1 @ X18))),
% 3.46/3.62      inference('cnf', [status(esa)], [t192_relat_1])).
% 3.46/3.62  thf('20', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 3.46/3.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.46/3.62  thf(t78_relat_1, axiom,
% 3.46/3.62    (![A:$i]:
% 3.46/3.62     ( ( v1_relat_1 @ A ) =>
% 3.46/3.62       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 3.46/3.62  thf('21', plain,
% 3.46/3.62      (![X29 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X29)) @ X29) = (X29))
% 3.46/3.62          | ~ (v1_relat_1 @ X29))),
% 3.46/3.62      inference('cnf', [status(esa)], [t78_relat_1])).
% 3.46/3.62  thf('22', plain,
% 3.46/3.62      (![X0 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 3.46/3.62            = (k6_relat_1 @ X0))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.46/3.62      inference('sup+', [status(thm)], ['20', '21'])).
% 3.46/3.62  thf('23', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('24', plain,
% 3.46/3.62      (![X0 : $i]:
% 3.46/3.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 3.46/3.62           = (k6_relat_1 @ X0))),
% 3.46/3.62      inference('demod', [status(thm)], ['22', '23'])).
% 3.46/3.62  thf('25', plain,
% 3.46/3.62      (![X31 : $i, X32 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.46/3.62          | ~ (v1_relat_1 @ X32))),
% 3.46/3.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.46/3.62  thf(t55_relat_1, axiom,
% 3.46/3.62    (![A:$i]:
% 3.46/3.62     ( ( v1_relat_1 @ A ) =>
% 3.46/3.62       ( ![B:$i]:
% 3.46/3.62         ( ( v1_relat_1 @ B ) =>
% 3.46/3.62           ( ![C:$i]:
% 3.46/3.62             ( ( v1_relat_1 @ C ) =>
% 3.46/3.62               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 3.46/3.62                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.46/3.62  thf('26', plain,
% 3.46/3.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.46/3.62         (~ (v1_relat_1 @ X20)
% 3.46/3.62          | ((k5_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 3.46/3.62              = (k5_relat_1 @ X21 @ (k5_relat_1 @ X20 @ X22)))
% 3.46/3.62          | ~ (v1_relat_1 @ X22)
% 3.46/3.62          | ~ (v1_relat_1 @ X21))),
% 3.46/3.62      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.46/3.62  thf('27', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 3.46/3.62          | ~ (v1_relat_1 @ X1)
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.46/3.62          | ~ (v1_relat_1 @ X2)
% 3.46/3.62          | ~ (v1_relat_1 @ X1))),
% 3.46/3.62      inference('sup+', [status(thm)], ['25', '26'])).
% 3.46/3.62  thf('28', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('29', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 3.46/3.62          | ~ (v1_relat_1 @ X1)
% 3.46/3.62          | ~ (v1_relat_1 @ X2)
% 3.46/3.62          | ~ (v1_relat_1 @ X1))),
% 3.46/3.62      inference('demod', [status(thm)], ['27', '28'])).
% 3.46/3.62  thf('30', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.62         (~ (v1_relat_1 @ X2)
% 3.46/3.62          | ~ (v1_relat_1 @ X1)
% 3.46/3.62          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.46/3.62              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 3.46/3.62      inference('simplify', [status(thm)], ['29'])).
% 3.46/3.62  thf('31', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 3.46/3.62            (k6_relat_1 @ X0))
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.46/3.62      inference('sup+', [status(thm)], ['24', '30'])).
% 3.46/3.62  thf('32', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('33', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('34', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 3.46/3.62           (k6_relat_1 @ X0))
% 3.46/3.62           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 3.46/3.62      inference('demod', [status(thm)], ['31', '32', '33'])).
% 3.46/3.62  thf('35', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 3.46/3.62            (k6_relat_1 @ X1))
% 3.46/3.62            = (k5_relat_1 @ 
% 3.46/3.62               (k6_relat_1 @ 
% 3.46/3.62                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 3.46/3.62               (k6_relat_1 @ X1)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.46/3.62      inference('sup+', [status(thm)], ['19', '34'])).
% 3.46/3.62  thf('36', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 3.46/3.62           (k6_relat_1 @ X0))
% 3.46/3.62           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 3.46/3.62      inference('demod', [status(thm)], ['31', '32', '33'])).
% 3.46/3.62  thf('37', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 3.46/3.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.46/3.62  thf('38', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('39', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.46/3.62           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.46/3.62              (k6_relat_1 @ X1)))),
% 3.46/3.62      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 3.46/3.62  thf('40', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.46/3.62            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.46/3.62      inference('sup+', [status(thm)], ['18', '39'])).
% 3.46/3.62  thf('41', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 3.46/3.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.46/3.62  thf('42', plain,
% 3.46/3.62      (![X18 : $i, X19 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X18 @ X19)
% 3.46/3.62            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19)))
% 3.46/3.62          | ~ (v1_relat_1 @ X18))),
% 3.46/3.62      inference('cnf', [status(esa)], [t192_relat_1])).
% 3.46/3.62  thf('43', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.46/3.62            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.46/3.62      inference('sup+', [status(thm)], ['41', '42'])).
% 3.46/3.62  thf('44', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('45', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.46/3.62           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 3.46/3.62      inference('demod', [status(thm)], ['43', '44'])).
% 3.46/3.62  thf('46', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('47', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.46/3.62           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.62      inference('demod', [status(thm)], ['40', '45', '46'])).
% 3.46/3.62  thf('48', plain,
% 3.46/3.62      (![X29 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X29)) @ X29) = (X29))
% 3.46/3.62          | ~ (v1_relat_1 @ X29))),
% 3.46/3.62      inference('cnf', [status(esa)], [t78_relat_1])).
% 3.46/3.62  thf('49', plain,
% 3.46/3.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.46/3.62         (~ (v1_relat_1 @ X20)
% 3.46/3.62          | ((k5_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 3.46/3.62              = (k5_relat_1 @ X21 @ (k5_relat_1 @ X20 @ X22)))
% 3.46/3.62          | ~ (v1_relat_1 @ X22)
% 3.46/3.62          | ~ (v1_relat_1 @ X21))),
% 3.46/3.62      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.46/3.62  thf('50', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k5_relat_1 @ X0 @ X1)
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 3.46/3.62               (k5_relat_1 @ X0 @ X1)))
% 3.46/3.62          | ~ (v1_relat_1 @ X0)
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 3.46/3.62          | ~ (v1_relat_1 @ X1)
% 3.46/3.62          | ~ (v1_relat_1 @ X0))),
% 3.46/3.62      inference('sup+', [status(thm)], ['48', '49'])).
% 3.46/3.62  thf('51', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('52', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k5_relat_1 @ X0 @ X1)
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 3.46/3.62               (k5_relat_1 @ X0 @ X1)))
% 3.46/3.62          | ~ (v1_relat_1 @ X0)
% 3.46/3.62          | ~ (v1_relat_1 @ X1)
% 3.46/3.62          | ~ (v1_relat_1 @ X0))),
% 3.46/3.62      inference('demod', [status(thm)], ['50', '51'])).
% 3.46/3.62  thf('53', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (~ (v1_relat_1 @ X1)
% 3.46/3.62          | ~ (v1_relat_1 @ X0)
% 3.46/3.62          | ((k5_relat_1 @ X0 @ X1)
% 3.46/3.62              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 3.46/3.62                 (k5_relat_1 @ X0 @ X1))))),
% 3.46/3.62      inference('simplify', [status(thm)], ['52'])).
% 3.46/3.62  thf('54', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 3.46/3.62               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.46/3.62      inference('sup+', [status(thm)], ['47', '53'])).
% 3.46/3.62  thf('55', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.46/3.62           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.62      inference('demod', [status(thm)], ['40', '45', '46'])).
% 3.46/3.62  thf('56', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 3.46/3.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.46/3.62  thf('57', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('58', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('59', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.62           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.46/3.62              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.62      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 3.46/3.62  thf('60', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k7_relat_1 @ (k6_relat_1 @ X1) @ 
% 3.46/3.62            (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 3.46/3.62            = (k5_relat_1 @ 
% 3.46/3.62               (k6_relat_1 @ 
% 3.46/3.62                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 3.46/3.62               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.46/3.62      inference('sup+', [status(thm)], ['17', '59'])).
% 3.46/3.62  thf('61', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 3.46/3.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.46/3.62  thf('62', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.46/3.62           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 3.46/3.62      inference('demod', [status(thm)], ['43', '44'])).
% 3.46/3.62  thf('63', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 3.46/3.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.46/3.62  thf('64', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('65', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.62           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.46/3.62              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.62      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 3.46/3.62  thf('66', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.46/3.62           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 3.46/3.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.46/3.62      inference('sup-', [status(thm)], ['6', '11'])).
% 3.46/3.62  thf('67', plain,
% 3.46/3.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.46/3.62         (~ (v1_relat_1 @ X20)
% 3.46/3.62          | ((k5_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 3.46/3.62              = (k5_relat_1 @ X21 @ (k5_relat_1 @ X20 @ X22)))
% 3.46/3.62          | ~ (v1_relat_1 @ X22)
% 3.46/3.62          | ~ (v1_relat_1 @ X21))),
% 3.46/3.62      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.46/3.62  thf('68', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 3.46/3.62               (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 3.46/3.62          | ~ (v1_relat_1 @ X2)
% 3.46/3.62          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.46/3.62      inference('sup+', [status(thm)], ['66', '67'])).
% 3.46/3.62  thf('69', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('70', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.62  thf('71', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 3.46/3.62               (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))
% 3.46/3.62          | ~ (v1_relat_1 @ X2))),
% 3.46/3.62      inference('demod', [status(thm)], ['68', '69', '70'])).
% 3.46/3.62  thf('72', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         (((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.46/3.62            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.46/3.62            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 3.46/3.62               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 3.46/3.62          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.62      inference('sup+', [status(thm)], ['65', '71'])).
% 3.46/3.62  thf('73', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.62           = (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.46/3.62              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.62      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 3.46/3.62  thf('74', plain,
% 3.46/3.62      (![X0 : $i, X1 : $i]:
% 3.46/3.62         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.46/3.62           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 3.46/3.62      inference('demod', [status(thm)], ['43', '44'])).
% 3.46/3.62  thf('75', plain,
% 3.46/3.62      (![X31 : $i, X32 : $i]:
% 3.46/3.62         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.46/3.62          | ~ (v1_relat_1 @ X32))),
% 3.46/3.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.46/3.63  thf(dt_k5_relat_1, axiom,
% 3.46/3.63    (![A:$i,B:$i]:
% 3.46/3.63     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 3.46/3.63       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 3.46/3.63  thf('76', plain,
% 3.46/3.63      (![X16 : $i, X17 : $i]:
% 3.46/3.63         (~ (v1_relat_1 @ X16)
% 3.46/3.63          | ~ (v1_relat_1 @ X17)
% 3.46/3.63          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 3.46/3.63      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.46/3.63  thf('77', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ X1)
% 3.46/3.63          | ~ (v1_relat_1 @ X1)
% 3.46/3.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.46/3.63      inference('sup+', [status(thm)], ['75', '76'])).
% 3.46/3.63  thf('78', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.63  thf('79', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ X1)
% 3.46/3.63          | ~ (v1_relat_1 @ X1))),
% 3.46/3.63      inference('demod', [status(thm)], ['77', '78'])).
% 3.46/3.63  thf('80', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.46/3.63      inference('simplify', [status(thm)], ['79'])).
% 3.46/3.63  thf('81', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.46/3.63      inference('sup+', [status(thm)], ['74', '80'])).
% 3.46/3.63  thf('82', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.63  thf('83', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['81', '82'])).
% 3.46/3.63  thf('84', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.63           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 3.46/3.63              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('demod', [status(thm)], ['72', '73', '83'])).
% 3.46/3.63  thf('85', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.46/3.63            = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 3.46/3.63      inference('sup+', [status(thm)], ['16', '84'])).
% 3.46/3.63  thf('86', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['81', '82'])).
% 3.46/3.63  thf('87', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.46/3.63           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['85', '86'])).
% 3.46/3.63  thf('88', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 3.46/3.63           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['40', '45', '46'])).
% 3.46/3.63  thf('89', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         (~ (v1_relat_1 @ X2)
% 3.46/3.63          | ~ (v1_relat_1 @ X1)
% 3.46/3.63          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.46/3.63              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 3.46/3.63      inference('simplify', [status(thm)], ['29'])).
% 3.46/3.63  thf('90', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 3.46/3.63            (k6_relat_1 @ X1))
% 3.46/3.63            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 3.46/3.63               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 3.46/3.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 3.46/3.63      inference('sup+', [status(thm)], ['88', '89'])).
% 3.46/3.63  thf('91', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.63  thf('92', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.63  thf('93', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 3.46/3.63           (k6_relat_1 @ X1))
% 3.46/3.63           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 3.46/3.63              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('demod', [status(thm)], ['90', '91', '92'])).
% 3.46/3.63  thf('94', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.63           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.46/3.63              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 3.46/3.63  thf('95', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         (~ (v1_relat_1 @ X2)
% 3.46/3.63          | ~ (v1_relat_1 @ X1)
% 3.46/3.63          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.46/3.63              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 3.46/3.63      inference('simplify', [status(thm)], ['29'])).
% 3.46/3.63  thf('96', plain,
% 3.46/3.63      (![X31 : $i, X32 : $i]:
% 3.46/3.63         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.46/3.63          | ~ (v1_relat_1 @ X32))),
% 3.46/3.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.46/3.63  thf('97', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 3.46/3.63            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ X2)
% 3.46/3.63          | ~ (v1_relat_1 @ X0)
% 3.46/3.63          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 3.46/3.63      inference('sup+', [status(thm)], ['95', '96'])).
% 3.46/3.63  thf('98', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.46/3.63          | ((k7_relat_1 @ 
% 3.46/3.63              (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.46/3.63               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 3.46/3.63              X2)
% 3.46/3.63              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 3.46/3.63                 (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 3.46/3.63      inference('sup-', [status(thm)], ['94', '97'])).
% 3.46/3.63  thf('99', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['81', '82'])).
% 3.46/3.63  thf('100', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['81', '82'])).
% 3.46/3.63  thf('101', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.63  thf('102', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.63           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.46/3.63              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 3.46/3.63  thf('103', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.63           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 3.46/3.63              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 3.46/3.63  thf('104', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         (~ (v1_relat_1 @ X2)
% 3.46/3.63          | ~ (v1_relat_1 @ X1)
% 3.46/3.63          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.46/3.63              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 3.46/3.63      inference('simplify', [status(thm)], ['29'])).
% 3.46/3.63  thf('105', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 3.46/3.63            (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.46/3.63            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 3.46/3.63               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 3.46/3.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('sup+', [status(thm)], ['103', '104'])).
% 3.46/3.63  thf('106', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 3.46/3.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 3.46/3.63  thf('107', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['81', '82'])).
% 3.46/3.63  thf('108', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 3.46/3.63           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.46/3.63           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 3.46/3.63              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('demod', [status(thm)], ['105', '106', '107'])).
% 3.46/3.63  thf('109', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 3.46/3.63           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 3.46/3.63              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('demod', [status(thm)],
% 3.46/3.63                ['98', '99', '100', '101', '102', '108'])).
% 3.46/3.63  thf('110', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 3.46/3.63           (k6_relat_1 @ X1))
% 3.46/3.63           = (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 3.46/3.63      inference('demod', [status(thm)], ['93', '109'])).
% 3.46/3.63  thf(t76_relat_1, axiom,
% 3.46/3.63    (![A:$i,B:$i]:
% 3.46/3.63     ( ( v1_relat_1 @ B ) =>
% 3.46/3.63       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 3.46/3.63         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 3.46/3.63  thf('111', plain,
% 3.46/3.63      (![X25 : $i, X26 : $i]:
% 3.46/3.63         ((r1_tarski @ (k5_relat_1 @ X25 @ (k6_relat_1 @ X26)) @ X25)
% 3.46/3.63          | ~ (v1_relat_1 @ X25))),
% 3.46/3.63      inference('cnf', [status(esa)], [t76_relat_1])).
% 3.46/3.63  thf('112', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         ((r1_tarski @ 
% 3.46/3.63           (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 3.46/3.63           (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 3.46/3.63          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 3.46/3.63      inference('sup+', [status(thm)], ['110', '111'])).
% 3.46/3.63  thf('113', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['81', '82'])).
% 3.46/3.63  thf('114', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.46/3.63         (r1_tarski @ 
% 3.46/3.63          (k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 3.46/3.63          (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 3.46/3.63      inference('demod', [status(thm)], ['112', '113'])).
% 3.46/3.63  thf('115', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 3.46/3.63          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 3.46/3.63      inference('sup+', [status(thm)], ['87', '114'])).
% 3.46/3.63  thf(d10_xboole_0, axiom,
% 3.46/3.63    (![A:$i,B:$i]:
% 3.46/3.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.46/3.63  thf('116', plain,
% 3.46/3.63      (![X0 : $i, X2 : $i]:
% 3.46/3.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.46/3.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.46/3.63  thf('117', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (~ (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 3.46/3.63             (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 3.46/3.63          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.63              = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 3.46/3.63      inference('sup-', [status(thm)], ['115', '116'])).
% 3.46/3.63  thf('118', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 3.46/3.63          (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 3.46/3.63      inference('sup+', [status(thm)], ['87', '114'])).
% 3.46/3.63  thf('119', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.63           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 3.46/3.63      inference('demod', [status(thm)], ['117', '118'])).
% 3.46/3.63  thf('120', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 3.46/3.63           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.46/3.63      inference('demod', [status(thm)], ['15', '119'])).
% 3.46/3.63  thf('121', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 3.46/3.63           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 3.46/3.63      inference('demod', [status(thm)], ['43', '44'])).
% 3.46/3.63  thf('122', plain,
% 3.46/3.63      (![X0 : $i, X1 : $i]:
% 3.46/3.63         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 3.46/3.63           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.46/3.63      inference('sup+', [status(thm)], ['120', '121'])).
% 3.46/3.63  thf('123', plain,
% 3.46/3.63      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 3.46/3.63         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 3.46/3.63      inference('demod', [status(thm)], ['4', '122'])).
% 3.46/3.63  thf('124', plain, ($false), inference('simplify', [status(thm)], ['123'])).
% 3.46/3.63  
% 3.46/3.63  % SZS output end Refutation
% 3.46/3.63  
% 3.46/3.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
