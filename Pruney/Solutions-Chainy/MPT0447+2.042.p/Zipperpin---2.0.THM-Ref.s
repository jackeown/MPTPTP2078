%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DHO7eRz7W8

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:58 EST 2020

% Result     : Theorem 51.91s
% Output     : Refutation 51.91s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 974 expanded)
%              Number of leaves         :   37 ( 329 expanded)
%              Depth                    :   34
%              Number of atoms          : 1430 (7660 expanded)
%              Number of equality atoms :   61 ( 401 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k3_tarski @ ( k2_tarski @ X10 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( r1_tarski @ ( k2_xboole_0 @ X27 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X27 @ X29 ) ) @ X28 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ X45 ) @ ( k1_relat_1 @ X45 ) ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['3','21'])).

thf('23',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X27 @ X29 ) ) @ X28 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('34',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('38',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X47 ) @ ( k1_relat_1 @ X46 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X47 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('49',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X47 ) @ ( k1_relat_1 @ X46 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X47 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('51',plain,(
    ! [X40: $i,X43: $i] :
      ( ( X43
        = ( k1_relat_1 @ X40 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X43 @ X40 ) @ ( sk_D_1 @ X43 @ X40 ) ) @ X40 )
      | ( r2_hidden @ ( sk_C_1 @ X43 @ X40 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('52',plain,(
    ! [X24: $i] :
      ( r1_xboole_0 @ X24 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('53',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X24: $i] :
      ( r1_xboole_0 @ X24 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('60',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('63',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('68',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('69',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('70',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('71',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['26','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('79',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('81',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('88',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('90',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('92',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('94',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('97',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_A ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('99',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['97','98'])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('100',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X49 @ X48 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X49 ) @ ( k2_relat_1 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf('101',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('102',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('103',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k2_relat_1 @ ( k3_tarski @ ( k2_tarski @ X49 @ X48 ) ) )
        = ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ X49 ) @ ( k2_relat_1 @ X48 ) ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) ) )
      = ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('108',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) ) )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('112',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k3_tarski @ ( k2_tarski @ X10 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['94','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('117',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','63','64','65'])).

thf('125',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('126',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('128',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k3_tarski @ ( k2_tarski @ X10 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('130',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X27 @ X29 ) ) @ X28 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ X1 ) ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) )
      | ~ ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['123','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('135',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('136',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ) @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('143',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('145',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('147',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('149',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_B_1 ) ) )
    = ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['133','134','149'])).

thf('151',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    $false ),
    inference(demod,[status(thm)],['0','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DHO7eRz7W8
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 51.91/52.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 51.91/52.09  % Solved by: fo/fo7.sh
% 51.91/52.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.91/52.09  % done 27931 iterations in 51.628s
% 51.91/52.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 51.91/52.09  % SZS output start Refutation
% 51.91/52.09  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 51.91/52.09  thf(sk_B_1_type, type, sk_B_1: $i).
% 51.91/52.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 51.91/52.09  thf(sk_B_type, type, sk_B: $i > $i).
% 51.91/52.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 51.91/52.09  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 51.91/52.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 51.91/52.09  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 51.91/52.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 51.91/52.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.91/52.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 51.91/52.09  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 51.91/52.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 51.91/52.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 51.91/52.09  thf(sk_A_type, type, sk_A: $i).
% 51.91/52.09  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 51.91/52.09  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 51.91/52.09  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 51.91/52.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 51.91/52.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.91/52.09  thf(t31_relat_1, conjecture,
% 51.91/52.09    (![A:$i]:
% 51.91/52.09     ( ( v1_relat_1 @ A ) =>
% 51.91/52.09       ( ![B:$i]:
% 51.91/52.09         ( ( v1_relat_1 @ B ) =>
% 51.91/52.09           ( ( r1_tarski @ A @ B ) =>
% 51.91/52.09             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 51.91/52.09  thf(zf_stmt_0, negated_conjecture,
% 51.91/52.09    (~( ![A:$i]:
% 51.91/52.09        ( ( v1_relat_1 @ A ) =>
% 51.91/52.09          ( ![B:$i]:
% 51.91/52.09            ( ( v1_relat_1 @ B ) =>
% 51.91/52.09              ( ( r1_tarski @ A @ B ) =>
% 51.91/52.09                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 51.91/52.09    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 51.91/52.09  thf('0', plain,
% 51.91/52.09      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf(d6_relat_1, axiom,
% 51.91/52.09    (![A:$i]:
% 51.91/52.09     ( ( v1_relat_1 @ A ) =>
% 51.91/52.09       ( ( k3_relat_1 @ A ) =
% 51.91/52.09         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 51.91/52.09  thf('1', plain,
% 51.91/52.09      (![X45 : $i]:
% 51.91/52.09         (((k3_relat_1 @ X45)
% 51.91/52.09            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 51.91/52.09          | ~ (v1_relat_1 @ X45))),
% 51.91/52.09      inference('cnf', [status(esa)], [d6_relat_1])).
% 51.91/52.09  thf(l51_zfmisc_1, axiom,
% 51.91/52.09    (![A:$i,B:$i]:
% 51.91/52.09     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 51.91/52.09  thf('2', plain,
% 51.91/52.09      (![X32 : $i, X33 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 51.91/52.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.91/52.09  thf('3', plain,
% 51.91/52.09      (![X45 : $i]:
% 51.91/52.09         (((k3_relat_1 @ X45)
% 51.91/52.09            = (k3_tarski @ 
% 51.91/52.09               (k2_tarski @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 51.91/52.09          | ~ (v1_relat_1 @ X45))),
% 51.91/52.09      inference('demod', [status(thm)], ['1', '2'])).
% 51.91/52.09  thf(t7_xboole_1, axiom,
% 51.91/52.09    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 51.91/52.09  thf('4', plain,
% 51.91/52.09      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 51.91/52.09      inference('cnf', [status(esa)], [t7_xboole_1])).
% 51.91/52.09  thf('5', plain,
% 51.91/52.09      (![X32 : $i, X33 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 51.91/52.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.91/52.09  thf('6', plain,
% 51.91/52.09      (![X25 : $i, X26 : $i]:
% 51.91/52.09         (r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X25 @ X26)))),
% 51.91/52.09      inference('demod', [status(thm)], ['4', '5'])).
% 51.91/52.09  thf(d10_xboole_0, axiom,
% 51.91/52.09    (![A:$i,B:$i]:
% 51.91/52.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 51.91/52.09  thf('7', plain,
% 51.91/52.09      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 51.91/52.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.91/52.09  thf('8', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 51.91/52.09      inference('simplify', [status(thm)], ['7'])).
% 51.91/52.09  thf(t10_xboole_1, axiom,
% 51.91/52.09    (![A:$i,B:$i,C:$i]:
% 51.91/52.09     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 51.91/52.09  thf('9', plain,
% 51.91/52.09      (![X8 : $i, X9 : $i, X10 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 51.91/52.09      inference('cnf', [status(esa)], [t10_xboole_1])).
% 51.91/52.09  thf('10', plain,
% 51.91/52.09      (![X32 : $i, X33 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 51.91/52.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.91/52.09  thf('11', plain,
% 51.91/52.09      (![X8 : $i, X9 : $i, X10 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X8 @ X9)
% 51.91/52.09          | (r1_tarski @ X8 @ (k3_tarski @ (k2_tarski @ X10 @ X9))))),
% 51.91/52.09      inference('demod', [status(thm)], ['9', '10'])).
% 51.91/52.09  thf('12', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['8', '11'])).
% 51.91/52.09  thf(t8_xboole_1, axiom,
% 51.91/52.09    (![A:$i,B:$i,C:$i]:
% 51.91/52.09     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 51.91/52.09       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 51.91/52.09  thf('13', plain,
% 51.91/52.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X27 @ X28)
% 51.91/52.09          | ~ (r1_tarski @ X29 @ X28)
% 51.91/52.09          | (r1_tarski @ (k2_xboole_0 @ X27 @ X29) @ X28))),
% 51.91/52.09      inference('cnf', [status(esa)], [t8_xboole_1])).
% 51.91/52.09  thf('14', plain,
% 51.91/52.09      (![X32 : $i, X33 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 51.91/52.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.91/52.09  thf('15', plain,
% 51.91/52.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X27 @ X28)
% 51.91/52.09          | ~ (r1_tarski @ X29 @ X28)
% 51.91/52.09          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X27 @ X29)) @ X28))),
% 51.91/52.09      inference('demod', [status(thm)], ['13', '14'])).
% 51.91/52.09  thf('16', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.91/52.09         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X2)) @ 
% 51.91/52.09           (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 51.91/52.09          | ~ (r1_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['12', '15'])).
% 51.91/52.09  thf('17', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ 
% 51.91/52.09          (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['6', '16'])).
% 51.91/52.09  thf('18', plain,
% 51.91/52.09      (![X5 : $i, X7 : $i]:
% 51.91/52.09         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 51.91/52.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.91/52.09  thf('19', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ 
% 51.91/52.09             (k3_tarski @ (k2_tarski @ X0 @ X1)))
% 51.91/52.09          | ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 51.91/52.09              = (k3_tarski @ (k2_tarski @ X0 @ X1))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['17', '18'])).
% 51.91/52.09  thf('20', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ 
% 51.91/52.09          (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['6', '16'])).
% 51.91/52.09  thf('21', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 51.91/52.09           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 51.91/52.09      inference('demod', [status(thm)], ['19', '20'])).
% 51.91/52.09  thf('22', plain,
% 51.91/52.09      (![X45 : $i]:
% 51.91/52.09         (((k3_relat_1 @ X45)
% 51.91/52.09            = (k3_tarski @ 
% 51.91/52.09               (k2_tarski @ (k2_relat_1 @ X45) @ (k1_relat_1 @ X45))))
% 51.91/52.09          | ~ (v1_relat_1 @ X45))),
% 51.91/52.09      inference('demod', [status(thm)], ['3', '21'])).
% 51.91/52.09  thf('23', plain,
% 51.91/52.09      (![X45 : $i]:
% 51.91/52.09         (((k3_relat_1 @ X45)
% 51.91/52.09            = (k3_tarski @ 
% 51.91/52.09               (k2_tarski @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 51.91/52.09          | ~ (v1_relat_1 @ X45))),
% 51.91/52.09      inference('demod', [status(thm)], ['1', '2'])).
% 51.91/52.09  thf('24', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['8', '11'])).
% 51.91/52.09  thf('25', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 51.91/52.09          | ~ (v1_relat_1 @ X0))),
% 51.91/52.09      inference('sup+', [status(thm)], ['23', '24'])).
% 51.91/52.09  thf('26', plain,
% 51.91/52.09      (![X45 : $i]:
% 51.91/52.09         (((k3_relat_1 @ X45)
% 51.91/52.09            = (k3_tarski @ 
% 51.91/52.09               (k2_tarski @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 51.91/52.09          | ~ (v1_relat_1 @ X45))),
% 51.91/52.09      inference('demod', [status(thm)], ['1', '2'])).
% 51.91/52.09  thf('27', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 51.91/52.09  thf('28', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 51.91/52.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 51.91/52.09  thf('29', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 51.91/52.09      inference('simplify', [status(thm)], ['7'])).
% 51.91/52.09  thf('30', plain,
% 51.91/52.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X27 @ X28)
% 51.91/52.09          | ~ (r1_tarski @ X29 @ X28)
% 51.91/52.09          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X27 @ X29)) @ X28))),
% 51.91/52.09      inference('demod', [status(thm)], ['13', '14'])).
% 51.91/52.09  thf('31', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 51.91/52.09          | ~ (r1_tarski @ X1 @ X0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['29', '30'])).
% 51.91/52.09  thf('32', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) @ X0)),
% 51.91/52.09      inference('sup-', [status(thm)], ['28', '31'])).
% 51.91/52.09  thf('33', plain,
% 51.91/52.09      (![X25 : $i, X26 : $i]:
% 51.91/52.09         (r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X25 @ X26)))),
% 51.91/52.09      inference('demod', [status(thm)], ['4', '5'])).
% 51.91/52.09  thf('34', plain,
% 51.91/52.09      (![X5 : $i, X7 : $i]:
% 51.91/52.09         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 51.91/52.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.91/52.09  thf('35', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 51.91/52.09          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['33', '34'])).
% 51.91/52.09  thf('36', plain,
% 51.91/52.09      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['32', '35'])).
% 51.91/52.09  thf(t43_xboole_1, axiom,
% 51.91/52.09    (![A:$i,B:$i,C:$i]:
% 51.91/52.09     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 51.91/52.09       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 51.91/52.09  thf('37', plain,
% 51.91/52.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 51.91/52.09         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 51.91/52.09          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 51.91/52.09      inference('cnf', [status(esa)], [t43_xboole_1])).
% 51.91/52.09  thf('38', plain,
% 51.91/52.09      (![X32 : $i, X33 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 51.91/52.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.91/52.09  thf('39', plain,
% 51.91/52.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 51.91/52.09         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 51.91/52.09          | ~ (r1_tarski @ X16 @ (k3_tarski @ (k2_tarski @ X17 @ X18))))),
% 51.91/52.09      inference('demod', [status(thm)], ['37', '38'])).
% 51.91/52.09  thf('40', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X1 @ X0)
% 51.91/52.09          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['36', '39'])).
% 51.91/52.09  thf('41', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ k1_xboole_0)),
% 51.91/52.09      inference('sup-', [status(thm)], ['27', '40'])).
% 51.91/52.09  thf('42', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 51.91/52.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 51.91/52.09  thf('43', plain,
% 51.91/52.09      (![X5 : $i, X7 : $i]:
% 51.91/52.09         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 51.91/52.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.91/52.09  thf('44', plain,
% 51.91/52.09      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['42', '43'])).
% 51.91/52.09  thf('45', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['41', '44'])).
% 51.91/52.09  thf(t15_relat_1, axiom,
% 51.91/52.09    (![A:$i]:
% 51.91/52.09     ( ( v1_relat_1 @ A ) =>
% 51.91/52.09       ( ![B:$i]:
% 51.91/52.09         ( ( v1_relat_1 @ B ) =>
% 51.91/52.09           ( r1_tarski @
% 51.91/52.09             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 51.91/52.09             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 51.91/52.09  thf('46', plain,
% 51.91/52.09      (![X46 : $i, X47 : $i]:
% 51.91/52.09         (~ (v1_relat_1 @ X46)
% 51.91/52.09          | (r1_tarski @ 
% 51.91/52.09             (k6_subset_1 @ (k1_relat_1 @ X47) @ (k1_relat_1 @ X46)) @ 
% 51.91/52.09             (k1_relat_1 @ (k6_subset_1 @ X47 @ X46)))
% 51.91/52.09          | ~ (v1_relat_1 @ X47))),
% 51.91/52.09      inference('cnf', [status(esa)], [t15_relat_1])).
% 51.91/52.09  thf(redefinition_k6_subset_1, axiom,
% 51.91/52.09    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 51.91/52.09  thf('47', plain,
% 51.91/52.09      (![X34 : $i, X35 : $i]:
% 51.91/52.09         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 51.91/52.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 51.91/52.09  thf('48', plain,
% 51.91/52.09      (![X34 : $i, X35 : $i]:
% 51.91/52.09         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 51.91/52.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 51.91/52.09  thf('49', plain,
% 51.91/52.09      (![X46 : $i, X47 : $i]:
% 51.91/52.09         (~ (v1_relat_1 @ X46)
% 51.91/52.09          | (r1_tarski @ 
% 51.91/52.09             (k4_xboole_0 @ (k1_relat_1 @ X47) @ (k1_relat_1 @ X46)) @ 
% 51.91/52.09             (k1_relat_1 @ (k4_xboole_0 @ X47 @ X46)))
% 51.91/52.09          | ~ (v1_relat_1 @ X47))),
% 51.91/52.09      inference('demod', [status(thm)], ['46', '47', '48'])).
% 51.91/52.09  thf('50', plain,
% 51.91/52.09      (((r1_tarski @ 
% 51.91/52.09         (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 51.91/52.09         (k1_relat_1 @ k1_xboole_0))
% 51.91/52.09        | ~ (v1_relat_1 @ sk_A)
% 51.91/52.09        | ~ (v1_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup+', [status(thm)], ['45', '49'])).
% 51.91/52.09  thf(d4_relat_1, axiom,
% 51.91/52.09    (![A:$i,B:$i]:
% 51.91/52.09     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 51.91/52.09       ( ![C:$i]:
% 51.91/52.09         ( ( r2_hidden @ C @ B ) <=>
% 51.91/52.09           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 51.91/52.09  thf('51', plain,
% 51.91/52.09      (![X40 : $i, X43 : $i]:
% 51.91/52.09         (((X43) = (k1_relat_1 @ X40))
% 51.91/52.09          | (r2_hidden @ 
% 51.91/52.09             (k4_tarski @ (sk_C_1 @ X43 @ X40) @ (sk_D_1 @ X43 @ X40)) @ X40)
% 51.91/52.09          | (r2_hidden @ (sk_C_1 @ X43 @ X40) @ X43))),
% 51.91/52.09      inference('cnf', [status(esa)], [d4_relat_1])).
% 51.91/52.09  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 51.91/52.09  thf('52', plain, (![X24 : $i]: (r1_xboole_0 @ X24 @ k1_xboole_0)),
% 51.91/52.09      inference('cnf', [status(esa)], [t65_xboole_1])).
% 51.91/52.09  thf(t7_xboole_0, axiom,
% 51.91/52.09    (![A:$i]:
% 51.91/52.09     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 51.91/52.09          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 51.91/52.09  thf('53', plain,
% 51.91/52.09      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 51.91/52.09      inference('cnf', [status(esa)], [t7_xboole_0])).
% 51.91/52.09  thf(t4_xboole_0, axiom,
% 51.91/52.09    (![A:$i,B:$i]:
% 51.91/52.09     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 51.91/52.09            ( r1_xboole_0 @ A @ B ) ) ) & 
% 51.91/52.09       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 51.91/52.09            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 51.91/52.09  thf('54', plain,
% 51.91/52.09      (![X0 : $i, X2 : $i, X3 : $i]:
% 51.91/52.09         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 51.91/52.09          | ~ (r1_xboole_0 @ X0 @ X3))),
% 51.91/52.09      inference('cnf', [status(esa)], [t4_xboole_0])).
% 51.91/52.09  thf('55', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['53', '54'])).
% 51.91/52.09  thf('56', plain,
% 51.91/52.09      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['52', '55'])).
% 51.91/52.09  thf('57', plain,
% 51.91/52.09      (![X0 : $i, X2 : $i, X3 : $i]:
% 51.91/52.09         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 51.91/52.09          | ~ (r1_xboole_0 @ X0 @ X3))),
% 51.91/52.09      inference('cnf', [status(esa)], [t4_xboole_0])).
% 51.91/52.09  thf('58', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['56', '57'])).
% 51.91/52.09  thf('59', plain, (![X24 : $i]: (r1_xboole_0 @ X24 @ k1_xboole_0)),
% 51.91/52.09      inference('cnf', [status(esa)], [t65_xboole_1])).
% 51.91/52.09  thf('60', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 51.91/52.09      inference('demod', [status(thm)], ['58', '59'])).
% 51.91/52.09  thf('61', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 51.91/52.09          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['51', '60'])).
% 51.91/52.09  thf('62', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 51.91/52.09      inference('demod', [status(thm)], ['58', '59'])).
% 51.91/52.09  thf('63', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['61', '62'])).
% 51.91/52.09  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('65', plain, ((v1_relat_1 @ sk_B_1)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('66', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 51.91/52.09        k1_xboole_0)),
% 51.91/52.09      inference('demod', [status(thm)], ['50', '63', '64', '65'])).
% 51.91/52.09  thf('67', plain,
% 51.91/52.09      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['42', '43'])).
% 51.91/52.09  thf('68', plain,
% 51.91/52.09      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))
% 51.91/52.09         = (k1_xboole_0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['66', '67'])).
% 51.91/52.09  thf(t44_xboole_1, axiom,
% 51.91/52.09    (![A:$i,B:$i,C:$i]:
% 51.91/52.09     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 51.91/52.09       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 51.91/52.09  thf('69', plain,
% 51.91/52.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.91/52.09         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 51.91/52.09          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 51.91/52.09      inference('cnf', [status(esa)], [t44_xboole_1])).
% 51.91/52.09  thf('70', plain,
% 51.91/52.09      (![X32 : $i, X33 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 51.91/52.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.91/52.09  thf('71', plain,
% 51.91/52.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.91/52.09         ((r1_tarski @ X19 @ (k3_tarski @ (k2_tarski @ X20 @ X21)))
% 51.91/52.09          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 51.91/52.09      inference('demod', [status(thm)], ['69', '70'])).
% 51.91/52.09  thf('72', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 51.91/52.09          | (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 51.91/52.09             (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ X0))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['68', '71'])).
% 51.91/52.09  thf('73', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 51.91/52.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 51.91/52.09  thf('74', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 51.91/52.09          (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ X0)))),
% 51.91/52.09      inference('demod', [status(thm)], ['72', '73'])).
% 51.91/52.09  thf('75', plain,
% 51.91/52.09      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 51.91/52.09        | ~ (v1_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup+', [status(thm)], ['26', '74'])).
% 51.91/52.09  thf('76', plain, ((v1_relat_1 @ sk_B_1)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('77', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('demod', [status(thm)], ['75', '76'])).
% 51.91/52.09  thf('78', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 51.91/52.09          | ~ (r1_tarski @ X1 @ X0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['29', '30'])).
% 51.91/52.09  thf('79', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))) @ 
% 51.91/52.09        (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['77', '78'])).
% 51.91/52.09  thf('80', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 51.91/52.09          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['33', '34'])).
% 51.91/52.09  thf('81', plain,
% 51.91/52.09      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)))
% 51.91/52.09         = (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['79', '80'])).
% 51.91/52.09  thf('82', plain,
% 51.91/52.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 51.91/52.09         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 51.91/52.09          | ~ (r1_tarski @ X16 @ (k3_tarski @ (k2_tarski @ X17 @ X18))))),
% 51.91/52.09      inference('demod', [status(thm)], ['37', '38'])).
% 51.91/52.09  thf('83', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1))
% 51.91/52.09          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_relat_1 @ sk_B_1)) @ 
% 51.91/52.09             (k1_relat_1 @ sk_A)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['81', '82'])).
% 51.91/52.09  thf('84', plain,
% 51.91/52.09      ((~ (v1_relat_1 @ sk_B_1)
% 51.91/52.09        | (r1_tarski @ 
% 51.91/52.09           (k4_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1)) @ 
% 51.91/52.09           (k1_relat_1 @ sk_A)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['25', '83'])).
% 51.91/52.09  thf('85', plain, ((v1_relat_1 @ sk_B_1)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('86', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k4_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1)) @ 
% 51.91/52.09        (k1_relat_1 @ sk_A))),
% 51.91/52.09      inference('demod', [status(thm)], ['84', '85'])).
% 51.91/52.09  thf('87', plain,
% 51.91/52.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.91/52.09         ((r1_tarski @ X19 @ (k3_tarski @ (k2_tarski @ X20 @ X21)))
% 51.91/52.09          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 51.91/52.09      inference('demod', [status(thm)], ['69', '70'])).
% 51.91/52.09  thf('88', plain,
% 51.91/52.09      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ 
% 51.91/52.09        (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['86', '87'])).
% 51.91/52.09  thf('89', plain,
% 51.91/52.09      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)))
% 51.91/52.09         = (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['79', '80'])).
% 51.91/52.09  thf('90', plain,
% 51.91/52.09      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('demod', [status(thm)], ['88', '89'])).
% 51.91/52.09  thf('91', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 51.91/52.09          | ~ (r1_tarski @ X1 @ X0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['29', '30'])).
% 51.91/52.09  thf('92', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k3_tarski @ 
% 51.91/52.09         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))) @ 
% 51.91/52.09        (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['90', '91'])).
% 51.91/52.09  thf('93', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 51.91/52.09          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['33', '34'])).
% 51.91/52.09  thf('94', plain,
% 51.91/52.09      (((k3_tarski @ 
% 51.91/52.09         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1)))
% 51.91/52.09         = (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['92', '93'])).
% 51.91/52.09  thf('95', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('96', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 51.91/52.09          | ~ (r1_tarski @ X1 @ X0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['29', '30'])).
% 51.91/52.09  thf('97', plain,
% 51.91/52.09      ((r1_tarski @ (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_A)) @ sk_B_1)),
% 51.91/52.09      inference('sup-', [status(thm)], ['95', '96'])).
% 51.91/52.09  thf('98', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 51.91/52.09          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['33', '34'])).
% 51.91/52.09  thf('99', plain, (((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_A)) = (sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['97', '98'])).
% 51.91/52.09  thf(t26_relat_1, axiom,
% 51.91/52.09    (![A:$i]:
% 51.91/52.09     ( ( v1_relat_1 @ A ) =>
% 51.91/52.09       ( ![B:$i]:
% 51.91/52.09         ( ( v1_relat_1 @ B ) =>
% 51.91/52.09           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 51.91/52.09             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 51.91/52.09  thf('100', plain,
% 51.91/52.09      (![X48 : $i, X49 : $i]:
% 51.91/52.09         (~ (v1_relat_1 @ X48)
% 51.91/52.09          | ((k2_relat_1 @ (k2_xboole_0 @ X49 @ X48))
% 51.91/52.09              = (k2_xboole_0 @ (k2_relat_1 @ X49) @ (k2_relat_1 @ X48)))
% 51.91/52.09          | ~ (v1_relat_1 @ X49))),
% 51.91/52.09      inference('cnf', [status(esa)], [t26_relat_1])).
% 51.91/52.09  thf('101', plain,
% 51.91/52.09      (![X32 : $i, X33 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 51.91/52.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.91/52.09  thf('102', plain,
% 51.91/52.09      (![X32 : $i, X33 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 51.91/52.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 51.91/52.09  thf('103', plain,
% 51.91/52.09      (![X48 : $i, X49 : $i]:
% 51.91/52.09         (~ (v1_relat_1 @ X48)
% 51.91/52.09          | ((k2_relat_1 @ (k3_tarski @ (k2_tarski @ X49 @ X48)))
% 51.91/52.09              = (k3_tarski @ 
% 51.91/52.09                 (k2_tarski @ (k2_relat_1 @ X49) @ (k2_relat_1 @ X48))))
% 51.91/52.09          | ~ (v1_relat_1 @ X49))),
% 51.91/52.09      inference('demod', [status(thm)], ['100', '101', '102'])).
% 51.91/52.09  thf('104', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 51.91/52.09          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['33', '34'])).
% 51.91/52.09  thf('105', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ (k2_relat_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))) @ 
% 51.91/52.09             (k2_relat_1 @ X1))
% 51.91/52.09          | ~ (v1_relat_1 @ X1)
% 51.91/52.09          | ~ (v1_relat_1 @ X0)
% 51.91/52.09          | ((k3_tarski @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 51.91/52.09              = (k2_relat_1 @ X1)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['103', '104'])).
% 51.91/52.09  thf('106', plain,
% 51.91/52.09      ((~ (r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_B_1))
% 51.91/52.09        | ((k3_tarski @ 
% 51.91/52.09            (k2_tarski @ (k2_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_A)))
% 51.91/52.09            = (k2_relat_1 @ sk_B_1))
% 51.91/52.09        | ~ (v1_relat_1 @ sk_A)
% 51.91/52.09        | ~ (v1_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['99', '105'])).
% 51.91/52.09  thf('107', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 51.91/52.09      inference('simplify', [status(thm)], ['7'])).
% 51.91/52.09  thf('108', plain, ((v1_relat_1 @ sk_A)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('109', plain, ((v1_relat_1 @ sk_B_1)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('110', plain,
% 51.91/52.09      (((k3_tarski @ (k2_tarski @ (k2_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_A)))
% 51.91/52.09         = (k2_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 51.91/52.09  thf('111', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['8', '11'])).
% 51.91/52.09  thf('112', plain,
% 51.91/52.09      (![X8 : $i, X9 : $i, X10 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X8 @ X9)
% 51.91/52.09          | (r1_tarski @ X8 @ (k3_tarski @ (k2_tarski @ X10 @ X9))))),
% 51.91/52.09      inference('demod', [status(thm)], ['9', '10'])).
% 51.91/52.09  thf('113', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.91/52.09         (r1_tarski @ X0 @ 
% 51.91/52.09          (k3_tarski @ (k2_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['111', '112'])).
% 51.91/52.09  thf('114', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 51.91/52.09          (k3_tarski @ (k2_tarski @ X0 @ (k2_relat_1 @ sk_B_1))))),
% 51.91/52.09      inference('sup+', [status(thm)], ['110', '113'])).
% 51.91/52.09  thf('115', plain,
% 51.91/52.09      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup+', [status(thm)], ['94', '114'])).
% 51.91/52.09  thf('116', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X1 @ X0)
% 51.91/52.09          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['36', '39'])).
% 51.91/52.09  thf('117', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)) @ 
% 51.91/52.09        k1_xboole_0)),
% 51.91/52.09      inference('sup-', [status(thm)], ['115', '116'])).
% 51.91/52.09  thf('118', plain,
% 51.91/52.09      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['42', '43'])).
% 51.91/52.09  thf('119', plain,
% 51.91/52.09      (((k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 51.91/52.09         = (k1_xboole_0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['117', '118'])).
% 51.91/52.09  thf('120', plain,
% 51.91/52.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.91/52.09         ((r1_tarski @ X19 @ (k3_tarski @ (k2_tarski @ X20 @ X21)))
% 51.91/52.09          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 51.91/52.09      inference('demod', [status(thm)], ['69', '70'])).
% 51.91/52.09  thf('121', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 51.91/52.09          | (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 51.91/52.09             (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ X0))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['119', '120'])).
% 51.91/52.09  thf('122', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 51.91/52.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 51.91/52.09  thf('123', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 51.91/52.09          (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ X0)))),
% 51.91/52.09      inference('demod', [status(thm)], ['121', '122'])).
% 51.91/52.09  thf('124', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1)) @ 
% 51.91/52.09        k1_xboole_0)),
% 51.91/52.09      inference('demod', [status(thm)], ['50', '63', '64', '65'])).
% 51.91/52.09  thf('125', plain,
% 51.91/52.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.91/52.09         ((r1_tarski @ X19 @ (k3_tarski @ (k2_tarski @ X20 @ X21)))
% 51.91/52.09          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 51.91/52.09      inference('demod', [status(thm)], ['69', '70'])).
% 51.91/52.09  thf('126', plain,
% 51.91/52.09      ((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 51.91/52.09        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['124', '125'])).
% 51.91/52.09  thf('127', plain,
% 51.91/52.09      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['32', '35'])).
% 51.91/52.09  thf('128', plain,
% 51.91/52.09      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('demod', [status(thm)], ['126', '127'])).
% 51.91/52.09  thf('129', plain,
% 51.91/52.09      (![X8 : $i, X9 : $i, X10 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X8 @ X9)
% 51.91/52.09          | (r1_tarski @ X8 @ (k3_tarski @ (k2_tarski @ X10 @ X9))))),
% 51.91/52.09      inference('demod', [status(thm)], ['9', '10'])).
% 51.91/52.09  thf('130', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 51.91/52.09          (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_1))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['128', '129'])).
% 51.91/52.09  thf('131', plain,
% 51.91/52.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X27 @ X28)
% 51.91/52.09          | ~ (r1_tarski @ X29 @ X28)
% 51.91/52.09          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X27 @ X29)) @ X28))),
% 51.91/52.09      inference('demod', [status(thm)], ['13', '14'])).
% 51.91/52.09  thf('132', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         ((r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ X1)) @ 
% 51.91/52.09           (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_1))))
% 51.91/52.09          | ~ (r1_tarski @ X1 @ 
% 51.91/52.09               (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_1)))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['130', '131'])).
% 51.91/52.09  thf('133', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) @ 
% 51.91/52.09        (k3_tarski @ 
% 51.91/52.09         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_B_1))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['123', '132'])).
% 51.91/52.09  thf('134', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 51.91/52.09           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 51.91/52.09      inference('demod', [status(thm)], ['19', '20'])).
% 51.91/52.09  thf('135', plain,
% 51.91/52.09      (![X45 : $i]:
% 51.91/52.09         (((k3_relat_1 @ X45)
% 51.91/52.09            = (k3_tarski @ 
% 51.91/52.09               (k2_tarski @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 51.91/52.09          | ~ (v1_relat_1 @ X45))),
% 51.91/52.09      inference('demod', [status(thm)], ['1', '2'])).
% 51.91/52.09  thf('136', plain,
% 51.91/52.09      (![X25 : $i, X26 : $i]:
% 51.91/52.09         (r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X25 @ X26)))),
% 51.91/52.09      inference('demod', [status(thm)], ['4', '5'])).
% 51.91/52.09  thf('137', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 51.91/52.09          | ~ (v1_relat_1 @ X0))),
% 51.91/52.09      inference('sup+', [status(thm)], ['135', '136'])).
% 51.91/52.09  thf('138', plain,
% 51.91/52.09      (![X0 : $i]:
% 51.91/52.09         (~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1))
% 51.91/52.09          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_relat_1 @ sk_B_1)) @ 
% 51.91/52.09             (k1_relat_1 @ sk_A)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['81', '82'])).
% 51.91/52.09  thf('139', plain,
% 51.91/52.09      ((~ (v1_relat_1 @ sk_B_1)
% 51.91/52.09        | (r1_tarski @ 
% 51.91/52.09           (k4_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1)) @ 
% 51.91/52.09           (k1_relat_1 @ sk_A)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['137', '138'])).
% 51.91/52.09  thf('140', plain, ((v1_relat_1 @ sk_B_1)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('141', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k4_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1)) @ 
% 51.91/52.09        (k1_relat_1 @ sk_A))),
% 51.91/52.09      inference('demod', [status(thm)], ['139', '140'])).
% 51.91/52.09  thf('142', plain,
% 51.91/52.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 51.91/52.09         ((r1_tarski @ X19 @ (k3_tarski @ (k2_tarski @ X20 @ X21)))
% 51.91/52.09          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 51.91/52.09      inference('demod', [status(thm)], ['69', '70'])).
% 51.91/52.09  thf('143', plain,
% 51.91/52.09      ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ 
% 51.91/52.09        (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))))),
% 51.91/52.09      inference('sup-', [status(thm)], ['141', '142'])).
% 51.91/52.09  thf('144', plain,
% 51.91/52.09      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)))
% 51.91/52.09         = (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['79', '80'])).
% 51.91/52.09  thf('145', plain,
% 51.91/52.09      ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('demod', [status(thm)], ['143', '144'])).
% 51.91/52.09  thf('146', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 51.91/52.09          | ~ (r1_tarski @ X1 @ X0))),
% 51.91/52.09      inference('sup-', [status(thm)], ['29', '30'])).
% 51.91/52.09  thf('147', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k3_tarski @ 
% 51.91/52.09         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_B_1))) @ 
% 51.91/52.09        (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['145', '146'])).
% 51.91/52.09  thf('148', plain,
% 51.91/52.09      (![X0 : $i, X1 : $i]:
% 51.91/52.09         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 51.91/52.09          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 51.91/52.09      inference('sup-', [status(thm)], ['33', '34'])).
% 51.91/52.09  thf('149', plain,
% 51.91/52.09      (((k3_tarski @ 
% 51.91/52.09         (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_B_1)))
% 51.91/52.09         = (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('sup-', [status(thm)], ['147', '148'])).
% 51.91/52.09  thf('150', plain,
% 51.91/52.09      ((r1_tarski @ 
% 51.91/52.09        (k3_tarski @ (k2_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))) @ 
% 51.91/52.09        (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('demod', [status(thm)], ['133', '134', '149'])).
% 51.91/52.09  thf('151', plain,
% 51.91/52.09      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 51.91/52.09        | ~ (v1_relat_1 @ sk_A))),
% 51.91/52.09      inference('sup+', [status(thm)], ['22', '150'])).
% 51.91/52.09  thf('152', plain, ((v1_relat_1 @ sk_A)),
% 51.91/52.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.91/52.09  thf('153', plain,
% 51.91/52.09      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 51.91/52.09      inference('demod', [status(thm)], ['151', '152'])).
% 51.91/52.09  thf('154', plain, ($false), inference('demod', [status(thm)], ['0', '153'])).
% 51.91/52.09  
% 51.91/52.09  % SZS output end Refutation
% 51.91/52.09  
% 51.91/52.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
