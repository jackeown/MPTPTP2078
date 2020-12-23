%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kdOSzUXOQA

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:47 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 196 expanded)
%              Number of leaves         :   30 (  74 expanded)
%              Depth                    :   23
%              Number of atoms          :  744 (1822 expanded)
%              Number of equality atoms :   40 ( 112 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t71_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X17 @ X22 )
      | ( X22
       != ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X17 @ ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X11: $i,X13: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X15 @ X11 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X17 @ ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) @ X0 @ X1 @ X2 @ X3 )
      | ( r1_tarski @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X18 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X18 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k2_enumset1 @ X21 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','37'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','44'])).

thf('46',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('51',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X31 ) )
      | ( r2_hidden @ X29 @ ( k1_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','54'])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('56',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X33 @ X34 ) @ X32 )
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
    = ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kdOSzUXOQA
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 259 iterations in 0.184s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(t71_funct_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.64       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.46/0.64         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.64          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.46/0.64            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.46/0.64              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t71_funct_1])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(commutativity_k2_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.64  thf(t12_setfam_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X25 : $i, X26 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X25 : $i, X26 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C_1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '5'])).
% 0.46/0.64  thf(t71_enumset1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.64         ((k2_enumset1 @ X8 @ X8 @ X9 @ X10) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.64  thf(d2_enumset1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.64     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.46/0.64       ( ![F:$i]:
% 0.46/0.64         ( ( r2_hidden @ F @ E ) <=>
% 0.46/0.64           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.46/0.64                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_2, axiom,
% 0.46/0.64    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.46/0.64       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.46/0.64         ( ( F ) != ( D ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_3, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.64     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.46/0.64       ( ![F:$i]:
% 0.46/0.64         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.46/0.64          | (r2_hidden @ X17 @ X22)
% 0.46/0.64          | ((X22) != (k2_enumset1 @ X21 @ X20 @ X19 @ X18)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.64         ((r2_hidden @ X17 @ (k2_enumset1 @ X21 @ X20 @ X19 @ X18))
% 0.46/0.64          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.46/0.64      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.46/0.64          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['7', '9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.64         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.64         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X15 @ X11)),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.64  thf(t70_enumset1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.64         ((r2_hidden @ X17 @ (k2_enumset1 @ X21 @ X20 @ X19 @ X18))
% 0.46/0.64          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.46/0.64      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.64  thf(d3_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X1 : $i, X3 : $i]:
% 0.46/0.64         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ (sk_C @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4) @ 
% 0.46/0.64           X0 @ X1 @ X2 @ X3)
% 0.46/0.64          | (r1_tarski @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X1 : $i, X3 : $i]:
% 0.46/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.64         ((k2_enumset1 @ X8 @ X8 @ X9 @ X10) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X23 @ X22)
% 0.46/0.64          | ~ (zip_tseitin_0 @ X23 @ X18 @ X19 @ X20 @ X21)
% 0.46/0.64          | ((X22) != (k2_enumset1 @ X21 @ X20 @ X19 @ X18)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.46/0.64         (~ (zip_tseitin_0 @ X23 @ X18 @ X19 @ X20 @ X21)
% 0.46/0.64          | ~ (r2_hidden @ X23 @ (k2_enumset1 @ X21 @ X20 @ X19 @ X18)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.46/0.64          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.64          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.46/0.64          | ~ (zip_tseitin_0 @ (sk_C @ X2 @ (k2_tarski @ X1 @ X0)) @ X0 @ X1 @ 
% 0.46/0.64               X1 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ (k2_tarski @ X0 @ X1) @ 
% 0.46/0.64           (k2_enumset1 @ X0 @ X0 @ X0 @ X1))
% 0.46/0.64          | (r1_tarski @ (k2_tarski @ X0 @ X1) @ 
% 0.46/0.64             (k2_enumset1 @ X0 @ X0 @ X0 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.64         ((k2_enumset1 @ X8 @ X8 @ X9 @ X10) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.64         ((k2_enumset1 @ X8 @ X8 @ X9 @ X10) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ (k2_tarski @ X0 @ X1) @ (k1_enumset1 @ X0 @ X0 @ X1))
% 0.46/0.64          | (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k1_enumset1 @ X0 @ X0 @ X1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['17', '33'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | (r2_hidden @ X0 @ X2)
% 0.46/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.64          | ~ (r2_hidden @ X2 @ (k2_tarski @ X0 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.46/0.64          | (r2_hidden @ X2 @ (k2_tarski @ X0 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['13', '37'])).
% 0.46/0.64  thf(t4_setfam_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_setfam_1 @ X27) @ X28) | ~ (r2_hidden @ X28 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | (r2_hidden @ X0 @ X2)
% 0.46/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.64  thf('45', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C_1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '5'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['46', '49'])).
% 0.46/0.64  thf(t86_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ C ) =>
% 0.46/0.64       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.46/0.64         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X29 @ X30)
% 0.46/0.64          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ X31))
% 0.46/0.64          | (r2_hidden @ X29 @ (k1_relat_1 @ (k7_relat_1 @ X31 @ X30)))
% 0.46/0.64          | ~ (v1_relat_1 @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ sk_C_1)
% 0.46/0.64          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ X0)))
% 0.46/0.64          | ~ (r2_hidden @ sk_A @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain, ((v1_relat_1 @ sk_C_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ X0)))
% 0.46/0.64          | ~ (r2_hidden @ sk_A @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['45', '54'])).
% 0.46/0.64  thf(t70_funct_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.64       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.46/0.64         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X32 @ (k1_relat_1 @ (k7_relat_1 @ X33 @ X34)))
% 0.46/0.64          | ((k1_funct_1 @ (k7_relat_1 @ X33 @ X34) @ X32)
% 0.46/0.64              = (k1_funct_1 @ X33 @ X32))
% 0.46/0.64          | ~ (v1_funct_1 @ X33)
% 0.46/0.64          | ~ (v1_relat_1 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C_1)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C_1)
% 0.46/0.64        | ((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 0.46/0.64            = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.64  thf('58', plain, ((v1_relat_1 @ sk_C_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 0.46/0.64         = (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 0.46/0.64         != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('62', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
