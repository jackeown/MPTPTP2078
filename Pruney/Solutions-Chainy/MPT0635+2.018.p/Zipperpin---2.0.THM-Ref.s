%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WEn3Cr6SIV

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:53 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 189 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  673 (1994 expanded)
%              Number of equality atoms :   41 ( 114 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t38_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ C @ A )
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['8','14'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('24',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X20 @ X19 ) @ X21 )
        = ( k1_funct_1 @ X19 @ ( k1_funct_1 @ X20 @ X21 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_B ) ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_B ) ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X23 ) @ X22 )
        = X22 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('33',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_B ) ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','48'])).

thf('50',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WEn3Cr6SIV
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.91/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.07  % Solved by: fo/fo7.sh
% 0.91/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.07  % done 1322 iterations in 0.625s
% 0.91/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.07  % SZS output start Refutation
% 0.91/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.07  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.91/1.07  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.07  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.91/1.07  thf(t38_funct_1, conjecture,
% 0.91/1.07    (![A:$i,B:$i,C:$i]:
% 0.91/1.07     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.07       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.91/1.07         ( ( k1_funct_1 @ C @ A ) =
% 0.91/1.07           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.91/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.07    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.07        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.07          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.91/1.07            ( ( k1_funct_1 @ C @ A ) =
% 0.91/1.07              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.91/1.07    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.91/1.07  thf('0', plain,
% 0.91/1.07      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf(t48_xboole_1, axiom,
% 0.91/1.07    (![A:$i,B:$i]:
% 0.91/1.07     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.07  thf('1', plain,
% 0.91/1.07      (![X6 : $i, X7 : $i]:
% 0.91/1.07         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.91/1.07           = (k3_xboole_0 @ X6 @ X7))),
% 0.91/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.07  thf(d5_xboole_0, axiom,
% 0.91/1.07    (![A:$i,B:$i,C:$i]:
% 0.91/1.07     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.91/1.07       ( ![D:$i]:
% 0.91/1.07         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.07           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.91/1.07  thf('2', plain,
% 0.91/1.07      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.07         (~ (r2_hidden @ X4 @ X3)
% 0.91/1.07          | (r2_hidden @ X4 @ X1)
% 0.91/1.07          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.07  thf('3', plain,
% 0.91/1.07      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.07         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.07      inference('simplify', [status(thm)], ['2'])).
% 0.91/1.07  thf('4', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.07         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.91/1.07      inference('sup-', [status(thm)], ['1', '3'])).
% 0.91/1.07  thf('5', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.91/1.07      inference('sup-', [status(thm)], ['0', '4'])).
% 0.91/1.07  thf('6', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.07         (~ (r2_hidden @ X0 @ X1)
% 0.91/1.07          | (r2_hidden @ X0 @ X2)
% 0.91/1.07          | (r2_hidden @ X0 @ X3)
% 0.91/1.07          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.07  thf('7', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.07         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.91/1.07          | (r2_hidden @ X0 @ X2)
% 0.91/1.07          | ~ (r2_hidden @ X0 @ X1))),
% 0.91/1.07      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.07  thf('8', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         ((r2_hidden @ sk_A @ X0)
% 0.91/1.07          | (r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_relat_1 @ sk_C) @ X0)))),
% 0.91/1.07      inference('sup-', [status(thm)], ['5', '7'])).
% 0.91/1.07  thf('9', plain,
% 0.91/1.07      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.91/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.07  thf('10', plain,
% 0.91/1.07      (![X6 : $i, X7 : $i]:
% 0.91/1.07         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.91/1.07           = (k3_xboole_0 @ X6 @ X7))),
% 0.91/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.07  thf('11', plain,
% 0.91/1.07      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.07         (~ (r2_hidden @ X4 @ X3)
% 0.91/1.07          | ~ (r2_hidden @ X4 @ X2)
% 0.91/1.07          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.07      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.07  thf('12', plain,
% 0.91/1.07      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.07         (~ (r2_hidden @ X4 @ X2)
% 0.91/1.07          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.07      inference('simplify', [status(thm)], ['11'])).
% 0.91/1.07  thf('13', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.07         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.07          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.07      inference('sup-', [status(thm)], ['10', '12'])).
% 0.91/1.07  thf('14', plain,
% 0.91/1.07      (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.91/1.07      inference('sup-', [status(thm)], ['9', '13'])).
% 0.91/1.07  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.91/1.07      inference('sup-', [status(thm)], ['8', '14'])).
% 0.91/1.07  thf('16', plain,
% 0.91/1.07      (![X6 : $i, X7 : $i]:
% 0.91/1.07         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.91/1.07           = (k3_xboole_0 @ X6 @ X7))),
% 0.91/1.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.07  thf('17', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.91/1.07      inference('sup-', [status(thm)], ['8', '14'])).
% 0.91/1.07  thf('18', plain,
% 0.91/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.07         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.91/1.07          | (r2_hidden @ X0 @ X2)
% 0.91/1.07          | ~ (r2_hidden @ X0 @ X1))),
% 0.91/1.07      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.07  thf('19', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         ((r2_hidden @ sk_A @ X0)
% 0.91/1.07          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.91/1.07      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.07  thf('20', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.91/1.07          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.91/1.07      inference('sup+', [status(thm)], ['16', '19'])).
% 0.91/1.07  thf('21', plain,
% 0.91/1.07      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.07         (~ (r2_hidden @ X4 @ X2)
% 0.91/1.07          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.07      inference('simplify', [status(thm)], ['11'])).
% 0.91/1.07  thf('22', plain,
% 0.91/1.07      (![X0 : $i]:
% 0.91/1.07         ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.91/1.07          | ~ (r2_hidden @ sk_A @ X0))),
% 0.91/1.07      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.07  thf('23', plain, ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B))),
% 0.91/1.08      inference('sup-', [status(thm)], ['15', '22'])).
% 0.91/1.08  thf(t71_relat_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.91/1.08       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.91/1.08  thf('24', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.91/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.08  thf(t23_funct_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.08       ( ![C:$i]:
% 0.91/1.08         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.08           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.91/1.08             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.91/1.08               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.91/1.08  thf('25', plain,
% 0.91/1.08      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X19)
% 0.91/1.08          | ~ (v1_funct_1 @ X19)
% 0.91/1.08          | ((k1_funct_1 @ (k5_relat_1 @ X20 @ X19) @ X21)
% 0.91/1.08              = (k1_funct_1 @ X19 @ (k1_funct_1 @ X20 @ X21)))
% 0.91/1.08          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 0.91/1.08          | ~ (v1_funct_1 @ X20)
% 0.91/1.08          | ~ (v1_relat_1 @ X20))),
% 0.91/1.08      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.91/1.08  thf('26', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (r2_hidden @ X1 @ X0)
% 0.91/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.91/1.08          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.91/1.08          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.91/1.08              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.91/1.08          | ~ (v1_funct_1 @ X2)
% 0.91/1.08          | ~ (v1_relat_1 @ X2))),
% 0.91/1.08      inference('sup-', [status(thm)], ['24', '25'])).
% 0.91/1.08  thf(fc3_funct_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.91/1.08       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.91/1.08  thf('27', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.08  thf('28', plain, (![X18 : $i]: (v1_funct_1 @ (k6_relat_1 @ X18))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.08  thf('29', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (r2_hidden @ X1 @ X0)
% 0.91/1.08          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.91/1.08              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.91/1.08          | ~ (v1_funct_1 @ X2)
% 0.91/1.08          | ~ (v1_relat_1 @ X2))),
% 0.91/1.08      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.91/1.08  thf('30', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X0)
% 0.91/1.08          | ~ (v1_funct_1 @ X0)
% 0.91/1.08          | ((k1_funct_1 @ 
% 0.91/1.08              (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ sk_B @ sk_B)) @ X0) @ 
% 0.91/1.08              sk_A)
% 0.91/1.08              = (k1_funct_1 @ X0 @ 
% 0.91/1.08                 (k1_funct_1 @ (k6_relat_1 @ (k3_xboole_0 @ sk_B @ sk_B)) @ 
% 0.91/1.08                  sk_A))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['23', '29'])).
% 0.91/1.08  thf('31', plain, ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B))),
% 0.91/1.08      inference('sup-', [status(thm)], ['15', '22'])).
% 0.91/1.08  thf(t35_funct_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( r2_hidden @ A @ B ) =>
% 0.91/1.08       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.91/1.08  thf('32', plain,
% 0.91/1.08      (![X22 : $i, X23 : $i]:
% 0.91/1.08         (((k1_funct_1 @ (k6_relat_1 @ X23) @ X22) = (X22))
% 0.91/1.08          | ~ (r2_hidden @ X22 @ X23))),
% 0.91/1.08      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.91/1.08  thf('33', plain,
% 0.91/1.08      (((k1_funct_1 @ (k6_relat_1 @ (k3_xboole_0 @ sk_B @ sk_B)) @ sk_A)
% 0.91/1.08         = (sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['31', '32'])).
% 0.91/1.08  thf('34', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X0)
% 0.91/1.08          | ~ (v1_funct_1 @ X0)
% 0.91/1.08          | ((k1_funct_1 @ 
% 0.91/1.08              (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ sk_B @ sk_B)) @ X0) @ 
% 0.91/1.08              sk_A) = (k1_funct_1 @ X0 @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['30', '33'])).
% 0.91/1.08  thf('35', plain,
% 0.91/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.08         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.91/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.91/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.08  thf('36', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.08          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.08      inference('eq_fact', [status(thm)], ['35'])).
% 0.91/1.08  thf('37', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.08          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.08      inference('eq_fact', [status(thm)], ['35'])).
% 0.91/1.08  thf('38', plain,
% 0.91/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.08         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.91/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.91/1.08          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.91/1.08          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.08  thf('39', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.91/1.08          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.08          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.91/1.08          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.08  thf('40', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.91/1.08          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.08          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.08      inference('simplify', [status(thm)], ['39'])).
% 0.91/1.08  thf('41', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.08          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.08      inference('eq_fact', [status(thm)], ['35'])).
% 0.91/1.08  thf('42', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.91/1.08          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.91/1.08      inference('clc', [status(thm)], ['40', '41'])).
% 0.91/1.08  thf('43', plain,
% 0.91/1.08      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.08         (~ (r2_hidden @ X4 @ X2)
% 0.91/1.08          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.08      inference('simplify', [status(thm)], ['11'])).
% 0.91/1.08  thf('44', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.91/1.08          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.08  thf('45', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.91/1.08          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['36', '44'])).
% 0.91/1.08  thf('46', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.08      inference('simplify', [status(thm)], ['45'])).
% 0.91/1.08  thf('47', plain,
% 0.91/1.08      (![X6 : $i, X7 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.91/1.08           = (k3_xboole_0 @ X6 @ X7))),
% 0.91/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.08  thf('48', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['46', '47'])).
% 0.91/1.08  thf('49', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ X0)
% 0.91/1.08          | ~ (v1_funct_1 @ X0)
% 0.91/1.08          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.91/1.08              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['34', '48'])).
% 0.91/1.08  thf('50', plain,
% 0.91/1.08      (((k1_funct_1 @ sk_C @ sk_A)
% 0.91/1.08         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('51', plain,
% 0.91/1.08      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 0.91/1.08        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.08        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.08      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.08  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('54', plain,
% 0.91/1.08      (((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))),
% 0.91/1.08      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.91/1.08  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.91/1.08  
% 0.91/1.08  % SZS output end Refutation
% 0.91/1.08  
% 0.91/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
