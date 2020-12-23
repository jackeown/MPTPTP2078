%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h6NU7Pw8jn

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:11 EST 2020

% Result     : Theorem 31.93s
% Output     : Refutation 31.93s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 207 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  829 (1522 expanded)
%              Number of equality atoms :   30 (  68 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X56: $i,X58: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X56 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ( v1_relat_1 @ X61 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X32 @ X31 )
      | ~ ( r1_tarski @ ( k2_tarski @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('11',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ ( k2_tarski @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X30 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r2_hidden @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X59: $i,X60: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( r1_tarski @ X59 @ X60 )
      | ( r1_tarski @ ( k1_setfam_1 @ X60 ) @ ( k1_setfam_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('30',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ( X14 = X15 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','34'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X34 @ X36 ) @ X35 )
       != ( k2_tarski @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['20','39'])).

thf('41',plain,(
    ! [X56: $i,X58: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X58 ) )
      | ~ ( r1_tarski @ X56 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ( v1_relat_1 @ X61 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('48',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X30 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r2_hidden @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X59: $i,X60: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( r1_tarski @ X59 @ X60 )
      | ( r1_tarski @ ( k1_setfam_1 @ X60 ) @ ( k1_setfam_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) )
      = ( k3_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ~ ( r1_tarski @ X64 @ X63 )
      | ( r1_tarski @ ( k5_relat_1 @ X65 @ X64 ) @ ( k5_relat_1 @ X65 @ X63 ) )
      | ~ ( v1_relat_1 @ X65 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('65',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ~ ( r1_tarski @ X64 @ X63 )
      | ( r1_tarski @ ( k5_relat_1 @ X65 @ X64 ) @ ( k5_relat_1 @ X65 @ X63 ) )
      | ~ ( v1_relat_1 @ X65 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('69',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('73',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['74','75','76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h6NU7Pw8jn
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:26:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 31.93/32.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.93/32.12  % Solved by: fo/fo7.sh
% 31.93/32.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.93/32.12  % done 11014 iterations in 31.663s
% 31.93/32.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.93/32.12  % SZS output start Refutation
% 31.93/32.12  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 31.93/32.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 31.93/32.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 31.93/32.12  thf(sk_C_type, type, sk_C: $i).
% 31.93/32.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 31.93/32.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 31.93/32.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.93/32.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 31.93/32.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 31.93/32.12  thf(sk_A_type, type, sk_A: $i).
% 31.93/32.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 31.93/32.12  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 31.93/32.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 31.93/32.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 31.93/32.12  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 31.93/32.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 31.93/32.12  thf(sk_B_type, type, sk_B: $i).
% 31.93/32.12  thf(t17_xboole_1, axiom,
% 31.93/32.12    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 31.93/32.12  thf('0', plain,
% 31.93/32.12      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 31.93/32.12      inference('cnf', [status(esa)], [t17_xboole_1])).
% 31.93/32.12  thf(t3_subset, axiom,
% 31.93/32.12    (![A:$i,B:$i]:
% 31.93/32.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 31.93/32.12  thf('1', plain,
% 31.93/32.12      (![X56 : $i, X58 : $i]:
% 31.93/32.12         ((m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X58)) | ~ (r1_tarski @ X56 @ X58))),
% 31.93/32.12      inference('cnf', [status(esa)], [t3_subset])).
% 31.93/32.12  thf('2', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['0', '1'])).
% 31.93/32.12  thf(cc2_relat_1, axiom,
% 31.93/32.12    (![A:$i]:
% 31.93/32.12     ( ( v1_relat_1 @ A ) =>
% 31.93/32.12       ( ![B:$i]:
% 31.93/32.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 31.93/32.12  thf('3', plain,
% 31.93/32.12      (![X61 : $i, X62 : $i]:
% 31.93/32.12         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 31.93/32.12          | (v1_relat_1 @ X61)
% 31.93/32.12          | ~ (v1_relat_1 @ X62))),
% 31.93/32.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 31.93/32.12  thf('4', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['2', '3'])).
% 31.93/32.12  thf(idempotence_k3_xboole_0, axiom,
% 31.93/32.12    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 31.93/32.12  thf('5', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 31.93/32.12      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 31.93/32.12  thf('6', plain,
% 31.93/32.12      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 31.93/32.12      inference('cnf', [status(esa)], [t17_xboole_1])).
% 31.93/32.12  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 31.93/32.12      inference('sup+', [status(thm)], ['5', '6'])).
% 31.93/32.12  thf(t38_zfmisc_1, axiom,
% 31.93/32.12    (![A:$i,B:$i,C:$i]:
% 31.93/32.12     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 31.93/32.12       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 31.93/32.12  thf('8', plain,
% 31.93/32.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 31.93/32.12         ((r2_hidden @ X32 @ X31)
% 31.93/32.12          | ~ (r1_tarski @ (k2_tarski @ X30 @ X32) @ X31))),
% 31.93/32.12      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 31.93/32.12  thf('9', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['7', '8'])).
% 31.93/32.12  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 31.93/32.12      inference('sup+', [status(thm)], ['5', '6'])).
% 31.93/32.12  thf('11', plain,
% 31.93/32.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 31.93/32.12         ((r2_hidden @ X30 @ X31)
% 31.93/32.12          | ~ (r1_tarski @ (k2_tarski @ X30 @ X32) @ X31))),
% 31.93/32.12      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 31.93/32.12  thf('12', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['10', '11'])).
% 31.93/32.12  thf('13', plain,
% 31.93/32.12      (![X30 : $i, X32 : $i, X33 : $i]:
% 31.93/32.12         ((r1_tarski @ (k2_tarski @ X30 @ X32) @ X33)
% 31.93/32.12          | ~ (r2_hidden @ X32 @ X33)
% 31.93/32.12          | ~ (r2_hidden @ X30 @ X33))),
% 31.93/32.12      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 31.93/32.12  thf('14', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 31.93/32.12          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['12', '13'])).
% 31.93/32.12  thf('15', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['9', '14'])).
% 31.93/32.12  thf(t7_setfam_1, axiom,
% 31.93/32.12    (![A:$i,B:$i]:
% 31.93/32.12     ( ( r1_tarski @ A @ B ) =>
% 31.93/32.12       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 31.93/32.12         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 31.93/32.12  thf('16', plain,
% 31.93/32.12      (![X59 : $i, X60 : $i]:
% 31.93/32.12         (((X59) = (k1_xboole_0))
% 31.93/32.12          | ~ (r1_tarski @ X59 @ X60)
% 31.93/32.12          | (r1_tarski @ (k1_setfam_1 @ X60) @ (k1_setfam_1 @ X59)))),
% 31.93/32.12      inference('cnf', [status(esa)], [t7_setfam_1])).
% 31.93/32.12  thf('17', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 31.93/32.12           (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 31.93/32.12          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['15', '16'])).
% 31.93/32.12  thf(t12_setfam_1, axiom,
% 31.93/32.12    (![A:$i,B:$i]:
% 31.93/32.12     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 31.93/32.12  thf('18', plain,
% 31.93/32.12      (![X54 : $i, X55 : $i]:
% 31.93/32.12         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 31.93/32.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.93/32.12  thf('19', plain,
% 31.93/32.12      (![X54 : $i, X55 : $i]:
% 31.93/32.12         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 31.93/32.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.93/32.12  thf('20', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 31.93/32.12          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 31.93/32.12      inference('demod', [status(thm)], ['17', '18', '19'])).
% 31.93/32.12  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 31.93/32.12      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 31.93/32.12  thf(t100_xboole_1, axiom,
% 31.93/32.12    (![A:$i,B:$i]:
% 31.93/32.12     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 31.93/32.12  thf('22', plain,
% 31.93/32.12      (![X1 : $i, X2 : $i]:
% 31.93/32.12         ((k4_xboole_0 @ X1 @ X2)
% 31.93/32.12           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 31.93/32.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 31.93/32.12  thf('23', plain,
% 31.93/32.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 31.93/32.12      inference('sup+', [status(thm)], ['21', '22'])).
% 31.93/32.12  thf(t36_xboole_1, axiom,
% 31.93/32.12    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 31.93/32.12  thf('24', plain,
% 31.93/32.12      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 31.93/32.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 31.93/32.12  thf(t79_xboole_1, axiom,
% 31.93/32.12    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 31.93/32.12  thf('25', plain,
% 31.93/32.12      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 31.93/32.12      inference('cnf', [status(esa)], [t79_xboole_1])).
% 31.93/32.12  thf(t69_xboole_1, axiom,
% 31.93/32.12    (![A:$i,B:$i]:
% 31.93/32.12     ( ( ~( v1_xboole_0 @ B ) ) =>
% 31.93/32.12       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 31.93/32.12  thf('26', plain,
% 31.93/32.12      (![X10 : $i, X11 : $i]:
% 31.93/32.12         (~ (r1_xboole_0 @ X10 @ X11)
% 31.93/32.12          | ~ (r1_tarski @ X10 @ X11)
% 31.93/32.12          | (v1_xboole_0 @ X10))),
% 31.93/32.12      inference('cnf', [status(esa)], [t69_xboole_1])).
% 31.93/32.12  thf('27', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 31.93/32.12          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['25', '26'])).
% 31.93/32.12  thf('28', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['24', '27'])).
% 31.93/32.12  thf('29', plain,
% 31.93/32.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 31.93/32.12      inference('sup+', [status(thm)], ['21', '22'])).
% 31.93/32.12  thf('30', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 31.93/32.12      inference('demod', [status(thm)], ['28', '29'])).
% 31.93/32.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 31.93/32.12  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 31.93/32.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 31.93/32.12  thf(t8_boole, axiom,
% 31.93/32.12    (![A:$i,B:$i]:
% 31.93/32.12     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 31.93/32.12  thf('32', plain,
% 31.93/32.12      (![X14 : $i, X15 : $i]:
% 31.93/32.12         (~ (v1_xboole_0 @ X14) | ~ (v1_xboole_0 @ X15) | ((X14) = (X15)))),
% 31.93/32.12      inference('cnf', [status(esa)], [t8_boole])).
% 31.93/32.12  thf('33', plain,
% 31.93/32.12      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['31', '32'])).
% 31.93/32.12  thf('34', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['30', '33'])).
% 31.93/32.12  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 31.93/32.12      inference('demod', [status(thm)], ['23', '34'])).
% 31.93/32.12  thf(t72_zfmisc_1, axiom,
% 31.93/32.12    (![A:$i,B:$i,C:$i]:
% 31.93/32.12     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 31.93/32.12       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 31.93/32.12  thf('36', plain,
% 31.93/32.12      (![X34 : $i, X35 : $i, X36 : $i]:
% 31.93/32.12         (~ (r2_hidden @ X34 @ X35)
% 31.93/32.12          | ((k4_xboole_0 @ (k2_tarski @ X34 @ X36) @ X35)
% 31.93/32.12              != (k2_tarski @ X34 @ X36)))),
% 31.93/32.12      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 31.93/32.12  thf('37', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 31.93/32.12          | ~ (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['35', '36'])).
% 31.93/32.12  thf('38', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['10', '11'])).
% 31.93/32.12  thf('39', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('demod', [status(thm)], ['37', '38'])).
% 31.93/32.12  thf('40', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))),
% 31.93/32.12      inference('clc', [status(thm)], ['20', '39'])).
% 31.93/32.12  thf('41', plain,
% 31.93/32.12      (![X56 : $i, X58 : $i]:
% 31.93/32.12         ((m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X58)) | ~ (r1_tarski @ X56 @ X58))),
% 31.93/32.12      inference('cnf', [status(esa)], [t3_subset])).
% 31.93/32.12  thf('42', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ 
% 31.93/32.12          (k1_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['40', '41'])).
% 31.93/32.12  thf('43', plain,
% 31.93/32.12      (![X61 : $i, X62 : $i]:
% 31.93/32.12         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 31.93/32.12          | (v1_relat_1 @ X61)
% 31.93/32.12          | ~ (v1_relat_1 @ X62))),
% 31.93/32.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 31.93/32.12  thf('44', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 31.93/32.12          | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['42', '43'])).
% 31.93/32.12  thf('45', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['4', '44'])).
% 31.93/32.12  thf('46', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['7', '8'])).
% 31.93/32.12  thf('47', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['7', '8'])).
% 31.93/32.12  thf('48', plain,
% 31.93/32.12      (![X30 : $i, X32 : $i, X33 : $i]:
% 31.93/32.12         ((r1_tarski @ (k2_tarski @ X30 @ X32) @ X33)
% 31.93/32.12          | ~ (r2_hidden @ X32 @ X33)
% 31.93/32.12          | ~ (r2_hidden @ X30 @ X33))),
% 31.93/32.12      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 31.93/32.12  thf('49', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 31.93/32.12          | (r1_tarski @ (k2_tarski @ X2 @ X0) @ (k2_tarski @ X1 @ X0)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['47', '48'])).
% 31.93/32.12  thf('50', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['46', '49'])).
% 31.93/32.12  thf('51', plain,
% 31.93/32.12      (![X59 : $i, X60 : $i]:
% 31.93/32.12         (((X59) = (k1_xboole_0))
% 31.93/32.12          | ~ (r1_tarski @ X59 @ X60)
% 31.93/32.12          | (r1_tarski @ (k1_setfam_1 @ X60) @ (k1_setfam_1 @ X59)))),
% 31.93/32.12      inference('cnf', [status(esa)], [t7_setfam_1])).
% 31.93/32.12  thf('52', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 31.93/32.12           (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))
% 31.93/32.12          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['50', '51'])).
% 31.93/32.12  thf('53', plain,
% 31.93/32.12      (![X54 : $i, X55 : $i]:
% 31.93/32.12         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 31.93/32.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.93/32.12  thf('54', plain,
% 31.93/32.12      (![X54 : $i, X55 : $i]:
% 31.93/32.12         ((k1_setfam_1 @ (k2_tarski @ X54 @ X55)) = (k3_xboole_0 @ X54 @ X55))),
% 31.93/32.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 31.93/32.12  thf('55', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 31.93/32.12      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 31.93/32.12  thf('56', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 31.93/32.12          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 31.93/32.12      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 31.93/32.12  thf('57', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 31.93/32.12      inference('demod', [status(thm)], ['37', '38'])).
% 31.93/32.12  thf('58', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 31.93/32.12      inference('clc', [status(thm)], ['56', '57'])).
% 31.93/32.12  thf(t48_relat_1, axiom,
% 31.93/32.12    (![A:$i]:
% 31.93/32.12     ( ( v1_relat_1 @ A ) =>
% 31.93/32.12       ( ![B:$i]:
% 31.93/32.12         ( ( v1_relat_1 @ B ) =>
% 31.93/32.12           ( ![C:$i]:
% 31.93/32.12             ( ( v1_relat_1 @ C ) =>
% 31.93/32.12               ( ( r1_tarski @ A @ B ) =>
% 31.93/32.12                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 31.93/32.12  thf('59', plain,
% 31.93/32.12      (![X63 : $i, X64 : $i, X65 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X63)
% 31.93/32.12          | ~ (r1_tarski @ X64 @ X63)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X65 @ X64) @ (k5_relat_1 @ X65 @ X63))
% 31.93/32.12          | ~ (v1_relat_1 @ X65)
% 31.93/32.12          | ~ (v1_relat_1 @ X64))),
% 31.93/32.12      inference('cnf', [status(esa)], [t48_relat_1])).
% 31.93/32.12  thf('60', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 31.93/32.12          | ~ (v1_relat_1 @ X2)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 31.93/32.12             (k5_relat_1 @ X2 @ X0))
% 31.93/32.12          | ~ (v1_relat_1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['58', '59'])).
% 31.93/32.12  thf('61', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X0)
% 31.93/32.12          | ~ (v1_relat_1 @ X0)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 31.93/32.12             (k5_relat_1 @ X2 @ X0))
% 31.93/32.12          | ~ (v1_relat_1 @ X2))),
% 31.93/32.12      inference('sup-', [status(thm)], ['45', '60'])).
% 31.93/32.12  thf('62', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X2)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 31.93/32.12             (k5_relat_1 @ X2 @ X0))
% 31.93/32.12          | ~ (v1_relat_1 @ X0))),
% 31.93/32.12      inference('simplify', [status(thm)], ['61'])).
% 31.93/32.12  thf('63', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 31.93/32.12      inference('sup-', [status(thm)], ['2', '3'])).
% 31.93/32.12  thf('64', plain,
% 31.93/32.12      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 31.93/32.12      inference('cnf', [status(esa)], [t17_xboole_1])).
% 31.93/32.12  thf('65', plain,
% 31.93/32.12      (![X63 : $i, X64 : $i, X65 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X63)
% 31.93/32.12          | ~ (r1_tarski @ X64 @ X63)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X65 @ X64) @ (k5_relat_1 @ X65 @ X63))
% 31.93/32.12          | ~ (v1_relat_1 @ X65)
% 31.93/32.12          | ~ (v1_relat_1 @ X64))),
% 31.93/32.12      inference('cnf', [status(esa)], [t48_relat_1])).
% 31.93/32.12  thf('66', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 31.93/32.12          | ~ (v1_relat_1 @ X2)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 31.93/32.12             (k5_relat_1 @ X2 @ X0))
% 31.93/32.12          | ~ (v1_relat_1 @ X0))),
% 31.93/32.12      inference('sup-', [status(thm)], ['64', '65'])).
% 31.93/32.12  thf('67', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X1)
% 31.93/32.12          | ~ (v1_relat_1 @ X1)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 31.93/32.12             (k5_relat_1 @ X2 @ X1))
% 31.93/32.12          | ~ (v1_relat_1 @ X2))),
% 31.93/32.12      inference('sup-', [status(thm)], ['63', '66'])).
% 31.93/32.12  thf('68', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X2)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 31.93/32.12             (k5_relat_1 @ X2 @ X1))
% 31.93/32.12          | ~ (v1_relat_1 @ X1))),
% 31.93/32.12      inference('simplify', [status(thm)], ['67'])).
% 31.93/32.12  thf(t19_xboole_1, axiom,
% 31.93/32.12    (![A:$i,B:$i,C:$i]:
% 31.93/32.12     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 31.93/32.12       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 31.93/32.12  thf('69', plain,
% 31.93/32.12      (![X5 : $i, X6 : $i, X7 : $i]:
% 31.93/32.12         (~ (r1_tarski @ X5 @ X6)
% 31.93/32.12          | ~ (r1_tarski @ X5 @ X7)
% 31.93/32.12          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 31.93/32.12      inference('cnf', [status(esa)], [t19_xboole_1])).
% 31.93/32.12  thf('70', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X0)
% 31.93/32.12          | ~ (v1_relat_1 @ X1)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 31.93/32.12             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 31.93/32.12          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 31.93/32.12      inference('sup-', [status(thm)], ['68', '69'])).
% 31.93/32.12  thf('71', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X0)
% 31.93/32.12          | ~ (v1_relat_1 @ X1)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 31.93/32.12             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 31.93/32.12          | ~ (v1_relat_1 @ X1)
% 31.93/32.12          | ~ (v1_relat_1 @ X2))),
% 31.93/32.12      inference('sup-', [status(thm)], ['62', '70'])).
% 31.93/32.12  thf('72', plain,
% 31.93/32.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.93/32.12         (~ (v1_relat_1 @ X2)
% 31.93/32.12          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 31.93/32.12             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 31.93/32.12          | ~ (v1_relat_1 @ X1)
% 31.93/32.12          | ~ (v1_relat_1 @ X0))),
% 31.93/32.12      inference('simplify', [status(thm)], ['71'])).
% 31.93/32.12  thf(t52_relat_1, conjecture,
% 31.93/32.12    (![A:$i]:
% 31.93/32.12     ( ( v1_relat_1 @ A ) =>
% 31.93/32.12       ( ![B:$i]:
% 31.93/32.12         ( ( v1_relat_1 @ B ) =>
% 31.93/32.12           ( ![C:$i]:
% 31.93/32.12             ( ( v1_relat_1 @ C ) =>
% 31.93/32.12               ( r1_tarski @
% 31.93/32.12                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 31.93/32.12                 ( k3_xboole_0 @
% 31.93/32.12                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 31.93/32.12  thf(zf_stmt_0, negated_conjecture,
% 31.93/32.12    (~( ![A:$i]:
% 31.93/32.12        ( ( v1_relat_1 @ A ) =>
% 31.93/32.12          ( ![B:$i]:
% 31.93/32.12            ( ( v1_relat_1 @ B ) =>
% 31.93/32.12              ( ![C:$i]:
% 31.93/32.12                ( ( v1_relat_1 @ C ) =>
% 31.93/32.12                  ( r1_tarski @
% 31.93/32.12                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 31.93/32.12                    ( k3_xboole_0 @
% 31.93/32.12                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 31.93/32.12    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 31.93/32.12  thf('73', plain,
% 31.93/32.12      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 31.93/32.12          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 31.93/32.12           (k5_relat_1 @ sk_A @ sk_C)))),
% 31.93/32.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.93/32.12  thf('74', plain,
% 31.93/32.12      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 31.93/32.12      inference('sup-', [status(thm)], ['72', '73'])).
% 31.93/32.12  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 31.93/32.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.93/32.12  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 31.93/32.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.93/32.12  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 31.93/32.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.93/32.12  thf('78', plain, ($false),
% 31.93/32.12      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 31.93/32.12  
% 31.93/32.12  % SZS output end Refutation
% 31.93/32.12  
% 31.96/32.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
