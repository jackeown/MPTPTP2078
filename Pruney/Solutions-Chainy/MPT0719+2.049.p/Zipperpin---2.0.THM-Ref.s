%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4l3aSFgCqW

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:32 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  157 (1303 expanded)
%              Number of leaves         :   38 ( 449 expanded)
%              Depth                    :   24
%              Number of atoms          : 1056 (9198 expanded)
%              Number of equality atoms :   74 ( 686 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('0',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X48 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_funct_1 @ X45 )
      | ( r2_hidden @ ( sk_C @ X45 @ X46 ) @ ( k1_relat_1 @ X45 ) )
      | ( v5_funct_1 @ X45 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v5_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X48: $i,X49: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('4',plain,(
    ! [X48: $i,X49: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v5_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X33: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != X40 )
      | ~ ( r2_hidden @ X38 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('15',plain,(
    ! [X39: $i,X40: $i] :
      ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t89_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t89_xboole_1])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X25 )
        = X24 )
      | ~ ( r1_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t89_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('47',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['44','47'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X37 ) )
      | ~ ( r1_xboole_0 @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X3 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      | ( r1_tarski @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','73'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','73'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X25 )
        = X24 )
      | ~ ( r1_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('90',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','73'])).

thf('93',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('96',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','98'])).

thf('100',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('103',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X48 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('105',plain,(
    ! [X44: $i] :
      ( ( ( k3_xboole_0 @ X44 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) )
        = X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) )
        = ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X48: $i,X49: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) )
      = ( sk_C_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('111',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','111'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('113',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['114','115','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4l3aSFgCqW
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 489 iterations in 0.206s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.66  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.44/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.66  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.44/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ?[C:$i]:
% 0.44/0.66       ( ( ![D:$i]:
% 0.44/0.66           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.44/0.66         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.44/0.66         ( v1_relat_1 @ C ) ) ))).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      (![X48 : $i, X49 : $i]: ((k1_relat_1 @ (sk_C_1 @ X48 @ X49)) = (X49))),
% 0.44/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.66  thf(d20_funct_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.66           ( ( v5_funct_1 @ B @ A ) <=>
% 0.44/0.66             ( ![C:$i]:
% 0.44/0.66               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.44/0.66                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      (![X45 : $i, X46 : $i]:
% 0.44/0.66         (~ (v1_relat_1 @ X45)
% 0.44/0.66          | ~ (v1_funct_1 @ X45)
% 0.44/0.66          | (r2_hidden @ (sk_C @ X45 @ X46) @ (k1_relat_1 @ X45))
% 0.44/0.66          | (v5_funct_1 @ X45 @ X46)
% 0.44/0.66          | ~ (v1_funct_1 @ X46)
% 0.44/0.66          | ~ (v1_relat_1 @ X46))),
% 0.44/0.66      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((r2_hidden @ (sk_C @ (sk_C_1 @ X1 @ X0) @ X2) @ X0)
% 0.44/0.66          | ~ (v1_relat_1 @ X2)
% 0.44/0.66          | ~ (v1_funct_1 @ X2)
% 0.44/0.66          | (v5_funct_1 @ (sk_C_1 @ X1 @ X0) @ X2)
% 0.44/0.66          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.44/0.66          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['0', '1'])).
% 0.44/0.66  thf('3', plain, (![X48 : $i, X49 : $i]: (v1_funct_1 @ (sk_C_1 @ X48 @ X49))),
% 0.44/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.66  thf('4', plain, (![X48 : $i, X49 : $i]: (v1_relat_1 @ (sk_C_1 @ X48 @ X49))),
% 0.44/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((r2_hidden @ (sk_C @ (sk_C_1 @ X1 @ X0) @ X2) @ X0)
% 0.44/0.66          | ~ (v1_relat_1 @ X2)
% 0.44/0.66          | ~ (v1_funct_1 @ X2)
% 0.44/0.66          | (v5_funct_1 @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.44/0.66      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.44/0.66  thf(t7_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.44/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.66  thf(t43_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.44/0.66       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.66         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.44/0.66          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.44/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.67  thf(t28_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.67  thf('9', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.67  thf('10', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.44/0.67           = (k4_xboole_0 @ X1 @ X1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.67  thf(t2_boole, axiom,
% 0.44/0.67    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.67  thf('11', plain,
% 0.44/0.67      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.67  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.67  thf(t76_enumset1, axiom,
% 0.44/0.67    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.67  thf('13', plain,
% 0.44/0.67      (![X33 : $i]: ((k1_enumset1 @ X33 @ X33 @ X33) = (k1_tarski @ X33))),
% 0.44/0.67      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.44/0.67  thf(t64_zfmisc_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.44/0.67       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.44/0.67  thf('14', plain,
% 0.44/0.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.44/0.67         (((X38) != (X40))
% 0.44/0.67          | ~ (r2_hidden @ X38 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40))))),
% 0.44/0.67      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.44/0.67  thf('15', plain,
% 0.44/0.67      (![X39 : $i, X40 : $i]:
% 0.44/0.67         ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X39 @ (k1_tarski @ X40)))),
% 0.44/0.67      inference('simplify', [status(thm)], ['14'])).
% 0.44/0.67  thf('16', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_enumset1 @ X0 @ X0 @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['13', '15'])).
% 0.44/0.67  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.67      inference('sup-', [status(thm)], ['12', '16'])).
% 0.44/0.67  thf('18', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((v5_funct_1 @ (sk_C_1 @ X1 @ k1_xboole_0) @ X0)
% 0.44/0.67          | ~ (v1_funct_1 @ X0)
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['5', '17'])).
% 0.44/0.67  thf('19', plain,
% 0.44/0.67      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.44/0.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.67  thf('20', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.67  thf('21', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.67  thf('22', plain,
% 0.44/0.67      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.67  thf(t89_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ))).
% 0.44/0.67  thf('23', plain,
% 0.44/0.67      (![X26 : $i, X27 : $i]:
% 0.44/0.67         (r1_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))),
% 0.44/0.67      inference('cnf', [status(esa)], [t89_xboole_1])).
% 0.44/0.67  thf(t74_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.44/0.67          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.44/0.67  thf('24', plain,
% 0.44/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.67         (~ (r1_xboole_0 @ X16 @ X17)
% 0.44/0.67          | (r1_xboole_0 @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.44/0.67  thf('25', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.44/0.67          (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 0.44/0.67      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.67  thf('26', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)),
% 0.44/0.67      inference('sup+', [status(thm)], ['22', '25'])).
% 0.44/0.67  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.44/0.67      inference('sup+', [status(thm)], ['21', '26'])).
% 0.44/0.67  thf(t88_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( r1_xboole_0 @ A @ B ) =>
% 0.44/0.67       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.44/0.67  thf('28', plain,
% 0.44/0.67      (![X24 : $i, X25 : $i]:
% 0.44/0.67         (((k4_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X25) = (X24))
% 0.44/0.67          | ~ (r1_xboole_0 @ X24 @ X25))),
% 0.44/0.67      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.44/0.67  thf('29', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.67  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.67  thf('31', plain,
% 0.44/0.67      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.67  thf(t52_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.44/0.67       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.44/0.67  thf('32', plain,
% 0.44/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.44/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 0.44/0.67              (k3_xboole_0 @ X13 @ X15)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.44/0.67  thf('33', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0))
% 0.44/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['31', '32'])).
% 0.44/0.67  thf('34', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.44/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['30', '33'])).
% 0.44/0.67  thf('35', plain,
% 0.44/0.67      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.44/0.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.67  thf('36', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (r1_tarski @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.44/0.67          (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['34', '35'])).
% 0.44/0.67  thf('37', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (r1_tarski @ X0 @ 
% 0.44/0.67          (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['29', '36'])).
% 0.44/0.67  thf('38', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.67  thf('39', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.67  thf('40', plain,
% 0.44/0.67      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.67  thf('41', plain,
% 0.44/0.67      (![X26 : $i, X27 : $i]:
% 0.44/0.67         (r1_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ (k4_xboole_0 @ X26 @ X27))),
% 0.44/0.67      inference('cnf', [status(esa)], [t89_xboole_1])).
% 0.44/0.67  thf('42', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['40', '41'])).
% 0.44/0.67  thf(t84_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.44/0.67          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.44/0.67  thf('43', plain,
% 0.44/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.67         ((r1_xboole_0 @ X21 @ X22)
% 0.44/0.67          | ~ (r1_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.44/0.67          | ~ (r1_xboole_0 @ X21 @ X23))),
% 0.44/0.67      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.44/0.67  thf('44', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.67          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.67  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.67  thf('46', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['40', '41'])).
% 0.44/0.67  thf('47', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.44/0.67      inference('sup+', [status(thm)], ['45', '46'])).
% 0.44/0.67  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.67      inference('demod', [status(thm)], ['44', '47'])).
% 0.44/0.67  thf(t127_zfmisc_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.67     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.44/0.67       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.44/0.67  thf('49', plain,
% 0.44/0.67      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.67         ((r1_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ (k2_zfmisc_1 @ X36 @ X37))
% 0.44/0.67          | ~ (r1_xboole_0 @ X34 @ X36))),
% 0.44/0.67      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.44/0.67  thf('50', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X2) @ 
% 0.44/0.67          (k2_zfmisc_1 @ X0 @ X1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['48', '49'])).
% 0.44/0.67  thf('51', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.67  thf('52', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.67  thf('53', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.67  thf('54', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.67  thf('55', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.67  thf('56', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.44/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['30', '33'])).
% 0.44/0.67  thf('57', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.44/0.67           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['55', '56'])).
% 0.44/0.67  thf('58', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.67  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['57', '58'])).
% 0.44/0.67  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['54', '59'])).
% 0.44/0.67  thf('61', plain,
% 0.44/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.44/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 0.44/0.67              (k3_xboole_0 @ X13 @ X15)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.44/0.67  thf('62', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.44/0.67           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.44/0.67      inference('sup+', [status(thm)], ['60', '61'])).
% 0.44/0.67  thf('63', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.44/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.67  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.67  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.67      inference('demod', [status(thm)], ['63', '64'])).
% 0.44/0.67  thf('66', plain,
% 0.44/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.67         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.44/0.67          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.44/0.67  thf('67', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ X0)),
% 0.44/0.67      inference('sup-', [status(thm)], ['65', '66'])).
% 0.44/0.67  thf('68', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.67  thf('69', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k3_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ X0)
% 0.44/0.67           = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.44/0.67  thf('70', plain,
% 0.44/0.67      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.67  thf('71', plain,
% 0.44/0.67      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['69', '70'])).
% 0.44/0.67  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['54', '59'])).
% 0.44/0.67  thf('73', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['62', '71', '72'])).
% 0.44/0.67  thf('74', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['53', '73'])).
% 0.44/0.67  thf('75', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.67  thf(t107_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.44/0.67       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.44/0.67         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.44/0.67  thf('76', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.44/0.67         ((r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X3))
% 0.44/0.67          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X3))
% 0.44/0.67          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X3)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.44/0.67  thf('77', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (~ (r1_xboole_0 @ X2 @ X0)
% 0.44/0.67          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))
% 0.44/0.67          | (r1_tarski @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['75', '76'])).
% 0.44/0.67  thf('78', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 0.44/0.67          | (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))
% 0.44/0.67          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['74', '77'])).
% 0.44/0.67  thf('79', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['53', '73'])).
% 0.44/0.67  thf('80', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['53', '73'])).
% 0.44/0.67  thf('81', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (r1_tarski @ X1 @ X0)
% 0.44/0.67          | (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.44/0.67          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.44/0.67  thf('82', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.67  thf('83', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.44/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.67  thf('84', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         ((r1_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.44/0.67          | ~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.44/0.67  thf('85', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['83', '84'])).
% 0.44/0.67  thf('86', plain, (![X0 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.44/0.67      inference('sup+', [status(thm)], ['82', '85'])).
% 0.44/0.67  thf('87', plain,
% 0.44/0.67      (![X24 : $i, X25 : $i]:
% 0.44/0.67         (((k4_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X25) = (X24))
% 0.44/0.67          | ~ (r1_xboole_0 @ X24 @ X25))),
% 0.44/0.67      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.44/0.67  thf('88', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) @ X0)
% 0.44/0.67           = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['86', '87'])).
% 0.44/0.67  thf('89', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.67  thf(t93_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( k2_xboole_0 @ A @ B ) =
% 0.44/0.67       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.67  thf('90', plain,
% 0.44/0.67      (![X28 : $i, X29 : $i]:
% 0.44/0.67         ((k2_xboole_0 @ X28 @ X29)
% 0.44/0.67           = (k2_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ 
% 0.44/0.67              (k3_xboole_0 @ X28 @ X29)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.44/0.67  thf('91', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k2_xboole_0 @ X0 @ X0)
% 0.44/0.67           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['89', '90'])).
% 0.44/0.67  thf('92', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['53', '73'])).
% 0.44/0.67  thf('93', plain,
% 0.44/0.67      (![X0 : $i]: ((X0) = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.44/0.67  thf('94', plain,
% 0.44/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['88', '93'])).
% 0.44/0.67  thf('95', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.67  thf('96', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['94', '95'])).
% 0.44/0.67  thf('97', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (r1_tarski @ X1 @ X0)
% 0.44/0.67          | (r1_tarski @ X1 @ k1_xboole_0)
% 0.44/0.67          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['81', '96'])).
% 0.44/0.67  thf('98', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         ((r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X2) @ k1_xboole_0)
% 0.44/0.67          | ~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X2) @ 
% 0.44/0.67               (k2_zfmisc_1 @ X1 @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['50', '97'])).
% 0.44/0.67  thf('99', plain,
% 0.44/0.67      (![X0 : $i]: (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.44/0.67      inference('sup-', [status(thm)], ['39', '98'])).
% 0.44/0.67  thf('100', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.67  thf('101', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k3_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.44/0.67           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['99', '100'])).
% 0.44/0.67  thf('102', plain,
% 0.44/0.67      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.67  thf('103', plain,
% 0.44/0.67      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['101', '102'])).
% 0.44/0.67  thf('104', plain,
% 0.44/0.67      (![X48 : $i, X49 : $i]: ((k1_relat_1 @ (sk_C_1 @ X48 @ X49)) = (X49))),
% 0.44/0.67      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.67  thf(t22_relat_1, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( v1_relat_1 @ A ) =>
% 0.44/0.67       ( ( k3_xboole_0 @
% 0.44/0.67           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.44/0.67         ( A ) ) ))).
% 0.44/0.67  thf('105', plain,
% 0.44/0.67      (![X44 : $i]:
% 0.44/0.67         (((k3_xboole_0 @ X44 @ 
% 0.44/0.67            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))) = (
% 0.44/0.67            X44))
% 0.44/0.67          | ~ (v1_relat_1 @ X44))),
% 0.44/0.67      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.44/0.67  thf('106', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k3_xboole_0 @ (sk_C_1 @ X1 @ X0) @ 
% 0.44/0.67            (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (sk_C_1 @ X1 @ X0))))
% 0.44/0.67            = (sk_C_1 @ X1 @ X0))
% 0.44/0.67          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0)))),
% 0.44/0.67      inference('sup+', [status(thm)], ['104', '105'])).
% 0.44/0.67  thf('107', plain,
% 0.44/0.67      (![X48 : $i, X49 : $i]: (v1_relat_1 @ (sk_C_1 @ X48 @ X49))),
% 0.44/0.67      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.44/0.67  thf('108', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((k3_xboole_0 @ (sk_C_1 @ X1 @ X0) @ 
% 0.44/0.67           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (sk_C_1 @ X1 @ X0))))
% 0.44/0.67           = (sk_C_1 @ X1 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['106', '107'])).
% 0.44/0.67  thf('109', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((k3_xboole_0 @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.44/0.67           = (sk_C_1 @ X0 @ k1_xboole_0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['103', '108'])).
% 0.44/0.67  thf('110', plain,
% 0.44/0.67      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.67  thf('111', plain,
% 0.44/0.67      (![X0 : $i]: ((k1_xboole_0) = (sk_C_1 @ X0 @ k1_xboole_0))),
% 0.44/0.67      inference('demod', [status(thm)], ['109', '110'])).
% 0.44/0.67  thf('112', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.44/0.67          | ~ (v1_funct_1 @ X0)
% 0.44/0.67          | ~ (v1_relat_1 @ X0))),
% 0.44/0.67      inference('demod', [status(thm)], ['18', '111'])).
% 0.44/0.67  thf(t174_funct_1, conjecture,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.67       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.44/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.67    (~( ![A:$i]:
% 0.44/0.67        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.67          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.44/0.67    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.44/0.67  thf('113', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('114', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['112', '113'])).
% 0.44/0.67  thf('115', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('116', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('117', plain, ($false),
% 0.44/0.67      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.44/0.67  
% 0.44/0.67  % SZS output end Refutation
% 0.44/0.67  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
