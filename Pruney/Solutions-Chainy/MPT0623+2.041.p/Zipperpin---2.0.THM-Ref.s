%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9rjxVSiiNE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 152 expanded)
%              Number of leaves         :   31 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  676 (1265 expanded)
%              Number of equality atoms :   84 ( 163 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X33 @ X34 ) )
        = X34 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X33 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( X26 = X23 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X33 @ X34 ) )
        = ( k1_tarski @ X33 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('29',plain,(
    ! [X35: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('35',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X30: $i] :
      ( ( ( k1_relat_1 @ X30 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X30 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( sk_B @ X31 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X35: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( sk_B @ X31 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('45',plain,(
    ! [X31: $i] :
      ( v1_funct_1 @ ( sk_B @ X31 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('46',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('47',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X33 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','57'])).

thf('59',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9rjxVSiiNE
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:52 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 230 iterations in 0.088s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.22/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.54  thf(t15_funct_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ?[C:$i]:
% 0.22/0.54           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.22/0.54             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.54             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (![X33 : $i, X34 : $i]:
% 0.22/0.54         (((k1_relat_1 @ (sk_C_3 @ X33 @ X34)) = (X34))
% 0.22/0.54          | ((X34) = (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X33 : $i, X34 : $i]:
% 0.22/0.54         ((v1_funct_1 @ (sk_C_3 @ X33 @ X34)) | ((X34) = (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.54  thf(d5_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.54       ( ![D:$i]:
% 0.22/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.22/0.54         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.22/0.54          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.22/0.54          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.54  thf('3', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 0.22/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.54  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 0.22/0.54      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.54  thf('5', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf(t83_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i]:
% 0.22/0.54         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 0.22/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf(t48_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.22/0.54           = (k3_xboole_0 @ X17 @ X18))),
% 0.22/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.22/0.54           = (k3_xboole_0 @ X17 @ X18))),
% 0.22/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.54           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf(t4_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.22/0.54          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.22/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.54          | ~ (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.22/0.54          | ~ (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf('16', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.54      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.22/0.54          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['2', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.22/0.54          | ((X1) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf(d3_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf(d1_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X26 @ X25)
% 0.22/0.54          | ((X26) = (X23))
% 0.22/0.54          | ((X25) != (k1_tarski @ X23)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X23 : $i, X26 : $i]:
% 0.22/0.54         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.54          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '22'])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.54          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.54          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((X0) = (k1_xboole_0))
% 0.22/0.54          | (r1_tarski @ (k1_tarski @ (sk_D @ X0 @ X1 @ k1_xboole_0)) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['19', '26'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X33 : $i, X34 : $i]:
% 0.22/0.54         (((k2_relat_1 @ (sk_C_3 @ X33 @ X34)) = (k1_tarski @ X33))
% 0.22/0.54          | ((X34) = (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.54  thf(t18_funct_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.54          ( ![C:$i]:
% 0.22/0.54            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.54              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.22/0.54                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i]:
% 0.22/0.54        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.54             ( ![C:$i]:
% 0.22/0.54               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.54                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.22/0.54                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X35 : $i]:
% 0.22/0.54         (~ (r1_tarski @ (k2_relat_1 @ X35) @ sk_A)
% 0.22/0.54          | ((sk_B_1) != (k1_relat_1 @ X35))
% 0.22/0.54          | ~ (v1_funct_1 @ X35)
% 0.22/0.54          | ~ (v1_relat_1 @ X35))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.22/0.54          | ((X1) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.22/0.54          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.22/0.54          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((sk_A) = (k1_xboole_0))
% 0.22/0.54          | ((sk_B_1)
% 0.22/0.54              != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1)))
% 0.22/0.54          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1))
% 0.22/0.54          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1))
% 0.22/0.54          | ((X1) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '30'])).
% 0.22/0.54  thf('32', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['32'])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['32'])).
% 0.22/0.54  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ?[B:$i]:
% 0.22/0.54       ( ( ![C:$i]:
% 0.22/0.54           ( ( r2_hidden @ C @ A ) =>
% 0.22/0.54             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.54         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.22/0.54         ( v1_relat_1 @ B ) ) ))).
% 0.22/0.54  thf('35', plain, (![X31 : $i]: ((k1_relat_1 @ (sk_B @ X31)) = (X31))),
% 0.22/0.54      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.54  thf(t65_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.54         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X30 : $i]:
% 0.22/0.54         (((k1_relat_1 @ X30) != (k1_xboole_0))
% 0.22/0.54          | ((k2_relat_1 @ X30) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X30))),
% 0.22/0.54      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((X0) != (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.22/0.54          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain, (![X31 : $i]: (v1_relat_1 @ (sk_B @ X31))),
% 0.22/0.54      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((X0) != (k1_xboole_0))
% 0.22/0.54          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.54  thf('40', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X35 : $i]:
% 0.22/0.54         (~ (r1_tarski @ (k2_relat_1 @ X35) @ sk_A)
% 0.22/0.54          | ((sk_B_1) != (k1_relat_1 @ X35))
% 0.22/0.54          | ~ (v1_funct_1 @ X35)
% 0.22/0.54          | ~ (v1_relat_1 @ X35))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.22/0.54        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.22/0.54        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.22/0.54        | ((sk_B_1) != (k1_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.54  thf('43', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.54  thf('44', plain, (![X31 : $i]: (v1_relat_1 @ (sk_B @ X31))),
% 0.22/0.54      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.54  thf('45', plain, (![X31 : $i]: (v1_funct_1 @ (sk_B @ X31))),
% 0.22/0.54      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.54  thf('46', plain, (![X31 : $i]: ((k1_relat_1 @ (sk_B @ X31)) = (X31))),
% 0.22/0.54      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.54  thf('47', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['34', '47'])).
% 0.22/0.54  thf('49', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.54      inference('split', [status(esa)], ['32'])).
% 0.22/0.54  thf('51', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.22/0.54  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['33', '51'])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((sk_B_1)
% 0.22/0.54            != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1)))
% 0.22/0.54          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1))
% 0.22/0.54          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ X1))
% 0.22/0.54          | ((X1) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['31', '52'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((X0) = (k1_xboole_0))
% 0.22/0.54          | ((X0) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ X0))
% 0.22/0.54          | ((sk_B_1)
% 0.22/0.54              != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ X0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '53'])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((sk_B_1)
% 0.22/0.54            != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ X0)))
% 0.22/0.54          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ X0))
% 0.22/0.54          | ((X0) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['54'])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X33 : $i, X34 : $i]:
% 0.22/0.54         ((v1_relat_1 @ (sk_C_3 @ X33 @ X34)) | ((X34) = (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((X0) = (k1_xboole_0))
% 0.22/0.54          | ((sk_B_1)
% 0.22/0.54              != (k1_relat_1 @ (sk_C_3 @ (sk_D @ sk_A @ X1 @ k1_xboole_0) @ X0))))),
% 0.22/0.54      inference('clc', [status(thm)], ['55', '56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '57'])).
% 0.22/0.54  thf('59', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.54  thf('60', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.22/0.54  thf('61', plain, ($false),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
