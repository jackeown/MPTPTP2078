%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rT8wygBP6S

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:29 EST 2020

% Result     : Theorem 2.74s
% Output     : Refutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  191 (2362 expanded)
%              Number of leaves         :   34 ( 686 expanded)
%              Depth                    :   56
%              Number of atoms          : 2001 (27881 expanded)
%              Number of equality atoms :  124 (1860 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X37 ) )
      | ~ ( v3_ordinal1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X37: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X37 ) )
      | ~ ( v3_ordinal1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31
       != ( k1_wellord2 @ X30 ) )
      | ( ( k3_relat_1 @ X31 )
        = X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('4',plain,(
    ! [X30: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X30 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
        = X30 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('5',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('6',plain,(
    ! [X30: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t36_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( r1_tarski @ A @ ( k3_relat_1 @ B ) )
          & ( v2_wellord1 @ B ) )
       => ( ~ ( ! [C: $i] :
                  ~ ( ( A
                      = ( k1_wellord1 @ B @ C ) )
                    & ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) )
              & ( A
               != ( k3_relat_1 @ B ) ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ! [D: $i] :
                  ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B )
                 => ( r2_hidden @ D @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ A )
       => ! [D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B )
           => ( r2_hidden @ D @ A ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k3_relat_1 @ B ) )
        & ( A
          = ( k1_wellord1 @ B @ C ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( v2_wellord1 @ B )
          & ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) )
       => ( ~ ( ( A
               != ( k3_relat_1 @ B ) )
              & ! [C: $i] :
                  ~ ( zip_tseitin_0 @ C @ B @ A ) )
        <=> ! [C: $i] :
              ( zip_tseitin_1 @ C @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( v2_wellord1 @ X20 )
      | ~ ( r1_tarski @ X21 @ ( k3_relat_1 @ X20 ) )
      | ( X21
       != ( k3_relat_1 @ X20 ) )
      | ( zip_tseitin_1 @ X23 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('8',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( zip_tseitin_1 @ X23 @ X20 @ ( k3_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X20 ) @ ( k3_relat_1 @ X20 ) )
      | ~ ( v2_wellord1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( zip_tseitin_1 @ X23 @ X20 @ ( k3_relat_1 @ X20 ) )
      | ~ ( v2_wellord1 @ X20 ) ) ),
    inference(demod,[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X37: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X37 ) )
      | ~ ( v3_ordinal1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('19',plain,(
    ! [X37: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X37 ) )
      | ~ ( v3_ordinal1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('20',plain,(
    ! [X30: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t41_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ( ! [C: $i] :
                ( ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                  & ( r1_tarski @ ( k1_wellord1 @ A @ C ) @ B ) )
               => ( r2_hidden @ C @ B ) )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ B ) ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_wellord1 @ X24 )
      | ( r2_hidden @ ( sk_C_2 @ X25 @ X24 ) @ ( k3_relat_1 @ X24 ) )
      | ( r1_tarski @ ( k3_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t41_wellord1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('24',plain,(
    ! [X30: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ( X36
        = ( k1_wellord1 @ ( k1_wellord2 @ X35 ) @ X36 ) )
      | ~ ( r2_hidden @ X36 @ X35 )
      | ~ ( v3_ordinal1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k1_wellord1 @ X7 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('32',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_wellord1 @ X7 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) @ ( k1_wellord2 @ X2 ) )
      | ~ ( v3_ordinal1 @ X2 )
      | ( X0 = X2 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ( X0 = X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) @ ( k1_wellord2 @ X2 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ X18 )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( zip_tseitin_1 @ X15 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k1_wellord2 @ X1 ) ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k1_wellord2 @ X1 ) ) @ X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k1_wellord2 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k1_wellord2 @ X1 ) ) @ X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k1_wellord2 @ X1 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_wellord1 @ X24 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X25 @ X24 ) @ X25 )
      | ( r1_tarski @ ( k3_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t41_wellord1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('47',plain,(
    ! [X30: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ X2 ) )
      | ~ ( v3_ordinal1 @ X2 )
      | ( X0 = X2 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ( X0 = X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_wellord2 @ X2 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ X18 )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( zip_tseitin_1 @ X15 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X3 )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( X1 = X2 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( X1 = X2 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('61',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X39 ) @ X38 )
        = ( k1_wellord2 @ X38 ) )
      | ~ ( r1_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X2 @ X1 )
      | ( X1 = X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ( X36
        = ( k1_wellord1 @ ( k1_wellord2 @ X35 ) @ X36 ) )
      | ~ ( r2_hidden @ X36 @ X35 )
      | ~ ( v3_ordinal1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k1_wellord1 @ X7 @ X6 ) )
      | ( X9 != X6 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_wellord1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X2 )
        = ( k1_wellord2 @ X2 ) )
      | ( X2 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X2 = X0 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( X1 = X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X2 = X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X2 )
        = ( k1_wellord2 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X39 ) @ X38 )
        = ( k1_wellord2 @ X38 ) )
      | ~ ( r1_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X2 )
        = ( k1_wellord2 @ X2 ) )
      | ( X2 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_wellord2 @ X0 )
       != ( k1_wellord2 @ X0 ) )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 )
        = ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(eq_fact,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 )
        = ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ( r2_hidden @ X4 @ X3 )
      | ( X4 = X3 )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('79',plain,(
    ! [X37: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X37 ) )
      | ~ ( v3_ordinal1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('80',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 )
        = ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_wellord1 @ X28 )
      | ~ ( r4_wellord1 @ X28 @ ( k2_wellord1 @ X28 @ ( k1_wellord1 @ X28 @ X29 ) ) )
      | ~ ( r2_hidden @ X29 @ ( k3_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('86',plain,(
    ! [X30: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('92',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('93',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','95'])).

thf('97',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('98',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['78','98'])).

thf('100',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('101',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ( X36
        = ( k1_wellord1 @ ( k1_wellord2 @ X35 ) @ X36 ) )
      | ~ ( r2_hidden @ X36 @ X35 )
      | ~ ( v3_ordinal1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('107',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('109',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('110',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_wellord1 @ X28 )
      | ~ ( r4_wellord1 @ X28 @ ( k2_wellord1 @ X28 @ ( k1_wellord1 @ X28 @ X29 ) ) )
      | ~ ( r2_hidden @ X29 @ ( k3_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('112',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('114',plain,(
    ! [X30: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('115',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('116',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','116'])).

thf('118',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('119',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( r4_wellord1 @ X26 @ X27 )
      | ~ ( r4_wellord1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('120',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('122',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('123',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('125',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('126',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','123','124','125'])).

thf('127',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('128',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','128'])).

thf('130',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('131',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ( X36
        = ( k1_wellord1 @ ( k1_wellord2 @ X35 ) @ X36 ) )
      | ~ ( r2_hidden @ X36 @ X35 )
      | ~ ( v3_ordinal1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('133',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('135',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('136',plain,
    ( sk_B
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k1_wellord1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('138',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_B )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('140',plain,(
    ~ ( r2_hidden @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('142',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['129','130'])).

thf('143',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('144',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_wellord1 @ X7 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ X18 )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( zip_tseitin_1 @ X15 @ X18 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ sk_A @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['141','150'])).

thf('152',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('153',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('154',plain,(
    r2_hidden @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['140','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rT8wygBP6S
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:13:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.74/2.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.74/2.98  % Solved by: fo/fo7.sh
% 2.74/2.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.74/2.98  % done 952 iterations in 2.530s
% 2.74/2.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.74/2.98  % SZS output start Refutation
% 2.74/2.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.74/2.98  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 2.74/2.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.74/2.98  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 2.74/2.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.74/2.98  thf(sk_A_type, type, sk_A: $i).
% 2.74/2.98  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 2.74/2.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 2.74/2.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.74/2.98  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.74/2.98  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 2.74/2.98  thf(sk_B_type, type, sk_B: $i).
% 2.74/2.98  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 2.74/2.98  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 2.74/2.98  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 2.74/2.98  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.74/2.98  thf(t7_wellord2, axiom,
% 2.74/2.98    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 2.74/2.98  thf('0', plain,
% 2.74/2.98      (![X37 : $i]:
% 2.74/2.98         ((v2_wellord1 @ (k1_wellord2 @ X37)) | ~ (v3_ordinal1 @ X37))),
% 2.74/2.98      inference('cnf', [status(esa)], [t7_wellord2])).
% 2.74/2.98  thf(t24_ordinal1, axiom,
% 2.74/2.98    (![A:$i]:
% 2.74/2.98     ( ( v3_ordinal1 @ A ) =>
% 2.74/2.98       ( ![B:$i]:
% 2.74/2.98         ( ( v3_ordinal1 @ B ) =>
% 2.74/2.98           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 2.74/2.98                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 2.74/2.98  thf('1', plain,
% 2.74/2.98      (![X3 : $i, X4 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X3)
% 2.74/2.98          | (r2_hidden @ X4 @ X3)
% 2.74/2.98          | ((X4) = (X3))
% 2.74/2.98          | (r2_hidden @ X3 @ X4)
% 2.74/2.98          | ~ (v3_ordinal1 @ X4))),
% 2.74/2.98      inference('cnf', [status(esa)], [t24_ordinal1])).
% 2.74/2.98  thf('2', plain,
% 2.74/2.98      (![X37 : $i]:
% 2.74/2.98         ((v2_wellord1 @ (k1_wellord2 @ X37)) | ~ (v3_ordinal1 @ X37))),
% 2.74/2.98      inference('cnf', [status(esa)], [t7_wellord2])).
% 2.74/2.98  thf(d1_wellord2, axiom,
% 2.74/2.98    (![A:$i,B:$i]:
% 2.74/2.98     ( ( v1_relat_1 @ B ) =>
% 2.74/2.98       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 2.74/2.98         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 2.74/2.98           ( ![C:$i,D:$i]:
% 2.74/2.98             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 2.74/2.98               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 2.74/2.98                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 2.74/2.98  thf('3', plain,
% 2.74/2.98      (![X30 : $i, X31 : $i]:
% 2.74/2.98         (((X31) != (k1_wellord2 @ X30))
% 2.74/2.98          | ((k3_relat_1 @ X31) = (X30))
% 2.74/2.98          | ~ (v1_relat_1 @ X31))),
% 2.74/2.98      inference('cnf', [status(esa)], [d1_wellord2])).
% 2.74/2.98  thf('4', plain,
% 2.74/2.98      (![X30 : $i]:
% 2.74/2.98         (~ (v1_relat_1 @ (k1_wellord2 @ X30))
% 2.74/2.98          | ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30)))),
% 2.74/2.98      inference('simplify', [status(thm)], ['3'])).
% 2.74/2.98  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 2.74/2.98  thf('5', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('6', plain, (![X30 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30))),
% 2.74/2.98      inference('demod', [status(thm)], ['4', '5'])).
% 2.74/2.98  thf(t36_wellord1, axiom,
% 2.74/2.98    (![A:$i,B:$i]:
% 2.74/2.98     ( ( v1_relat_1 @ B ) =>
% 2.74/2.98       ( ( ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) & ( v2_wellord1 @ B ) ) =>
% 2.74/2.98         ( ( ~( ( ![C:$i]:
% 2.74/2.98                  ( ~( ( ( A ) = ( k1_wellord1 @ B @ C ) ) & 
% 2.74/2.98                       ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) ) ) ) & 
% 2.74/2.98                ( ( A ) != ( k3_relat_1 @ B ) ) ) ) <=>
% 2.74/2.98           ( ![C:$i]:
% 2.74/2.98             ( ( r2_hidden @ C @ A ) =>
% 2.74/2.98               ( ![D:$i]:
% 2.74/2.98                 ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) =>
% 2.74/2.98                   ( r2_hidden @ D @ A ) ) ) ) ) ) ) ))).
% 2.74/2.98  thf(zf_stmt_0, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.74/2.98  thf(zf_stmt_1, axiom,
% 2.74/2.98    (![C:$i,B:$i,A:$i]:
% 2.74/2.98     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 2.74/2.98       ( ( r2_hidden @ C @ A ) =>
% 2.74/2.98         ( ![D:$i]:
% 2.74/2.98           ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) => ( r2_hidden @ D @ A ) ) ) ) ))).
% 2.74/2.98  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $o).
% 2.74/2.98  thf(zf_stmt_3, axiom,
% 2.74/2.98    (![C:$i,B:$i,A:$i]:
% 2.74/2.98     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 2.74/2.98       ( ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) & 
% 2.74/2.98         ( ( A ) = ( k1_wellord1 @ B @ C ) ) ) ))).
% 2.74/2.98  thf(zf_stmt_4, axiom,
% 2.74/2.98    (![A:$i,B:$i]:
% 2.74/2.98     ( ( v1_relat_1 @ B ) =>
% 2.74/2.98       ( ( ( v2_wellord1 @ B ) & ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) ) =>
% 2.74/2.98         ( ( ~( ( ( A ) != ( k3_relat_1 @ B ) ) & 
% 2.74/2.98                ( ![C:$i]: ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ) ) <=>
% 2.74/2.98           ( ![C:$i]: ( zip_tseitin_1 @ C @ B @ A ) ) ) ) ))).
% 2.74/2.98  thf('7', plain,
% 2.74/2.98      (![X20 : $i, X21 : $i, X23 : $i]:
% 2.74/2.98         (~ (v2_wellord1 @ X20)
% 2.74/2.98          | ~ (r1_tarski @ X21 @ (k3_relat_1 @ X20))
% 2.74/2.98          | ((X21) != (k3_relat_1 @ X20))
% 2.74/2.98          | (zip_tseitin_1 @ X23 @ X20 @ X21)
% 2.74/2.98          | ~ (v1_relat_1 @ X20))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.74/2.98  thf('8', plain,
% 2.74/2.98      (![X20 : $i, X23 : $i]:
% 2.74/2.98         (~ (v1_relat_1 @ X20)
% 2.74/2.98          | (zip_tseitin_1 @ X23 @ X20 @ (k3_relat_1 @ X20))
% 2.74/2.98          | ~ (r1_tarski @ (k3_relat_1 @ X20) @ (k3_relat_1 @ X20))
% 2.74/2.98          | ~ (v2_wellord1 @ X20))),
% 2.74/2.98      inference('simplify', [status(thm)], ['7'])).
% 2.74/2.98  thf(d10_xboole_0, axiom,
% 2.74/2.98    (![A:$i,B:$i]:
% 2.74/2.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.74/2.98  thf('9', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.74/2.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.74/2.98  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.74/2.98      inference('simplify', [status(thm)], ['9'])).
% 2.74/2.98  thf('11', plain,
% 2.74/2.98      (![X20 : $i, X23 : $i]:
% 2.74/2.98         (~ (v1_relat_1 @ X20)
% 2.74/2.98          | (zip_tseitin_1 @ X23 @ X20 @ (k3_relat_1 @ X20))
% 2.74/2.98          | ~ (v2_wellord1 @ X20))),
% 2.74/2.98      inference('demod', [status(thm)], ['8', '10'])).
% 2.74/2.98  thf('12', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         ((zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 2.74/2.98          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 2.74/2.98      inference('sup+', [status(thm)], ['6', '11'])).
% 2.74/2.98  thf('13', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('14', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         ((zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X0)))),
% 2.74/2.98      inference('demod', [status(thm)], ['12', '13'])).
% 2.74/2.98  thf('15', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0) | (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['2', '14'])).
% 2.74/2.98  thf('16', plain,
% 2.74/2.98      (![X37 : $i]:
% 2.74/2.98         ((v2_wellord1 @ (k1_wellord2 @ X37)) | ~ (v3_ordinal1 @ X37))),
% 2.74/2.98      inference('cnf', [status(esa)], [t7_wellord2])).
% 2.74/2.98  thf('17', plain,
% 2.74/2.98      (![X3 : $i, X4 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X3)
% 2.74/2.98          | (r2_hidden @ X4 @ X3)
% 2.74/2.98          | ((X4) = (X3))
% 2.74/2.98          | (r2_hidden @ X3 @ X4)
% 2.74/2.98          | ~ (v3_ordinal1 @ X4))),
% 2.74/2.98      inference('cnf', [status(esa)], [t24_ordinal1])).
% 2.74/2.98  thf('18', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0) | (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['2', '14'])).
% 2.74/2.98  thf('19', plain,
% 2.74/2.98      (![X37 : $i]:
% 2.74/2.98         ((v2_wellord1 @ (k1_wellord2 @ X37)) | ~ (v3_ordinal1 @ X37))),
% 2.74/2.98      inference('cnf', [status(esa)], [t7_wellord2])).
% 2.74/2.98  thf('20', plain, (![X30 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30))),
% 2.74/2.98      inference('demod', [status(thm)], ['4', '5'])).
% 2.74/2.98  thf(t41_wellord1, axiom,
% 2.74/2.98    (![A:$i]:
% 2.74/2.98     ( ( v1_relat_1 @ A ) =>
% 2.74/2.98       ( ( v2_wellord1 @ A ) =>
% 2.74/2.98         ( ![B:$i]:
% 2.74/2.98           ( ( ![C:$i]:
% 2.74/2.98               ( ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & 
% 2.74/2.98                   ( r1_tarski @ ( k1_wellord1 @ A @ C ) @ B ) ) =>
% 2.74/2.98                 ( r2_hidden @ C @ B ) ) ) =>
% 2.74/2.98             ( r1_tarski @ ( k3_relat_1 @ A ) @ B ) ) ) ) ))).
% 2.74/2.98  thf('21', plain,
% 2.74/2.98      (![X24 : $i, X25 : $i]:
% 2.74/2.98         (~ (v2_wellord1 @ X24)
% 2.74/2.98          | (r2_hidden @ (sk_C_2 @ X25 @ X24) @ (k3_relat_1 @ X24))
% 2.74/2.98          | (r1_tarski @ (k3_relat_1 @ X24) @ X25)
% 2.74/2.98          | ~ (v1_relat_1 @ X24))),
% 2.74/2.98      inference('cnf', [status(esa)], [t41_wellord1])).
% 2.74/2.98  thf('22', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         ((r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 2.74/2.98          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 2.74/2.98          | (r1_tarski @ (k3_relat_1 @ (k1_wellord2 @ X0)) @ X1)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X0)))),
% 2.74/2.98      inference('sup+', [status(thm)], ['20', '21'])).
% 2.74/2.98  thf('23', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('24', plain, (![X30 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30))),
% 2.74/2.98      inference('demod', [status(thm)], ['4', '5'])).
% 2.74/2.98  thf('25', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         ((r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 2.74/2.98          | (r1_tarski @ X0 @ X1)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X0)))),
% 2.74/2.98      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.74/2.98  thf('26', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r1_tarski @ X0 @ X1)
% 2.74/2.98          | (r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['19', '25'])).
% 2.74/2.98  thf('27', plain,
% 2.74/2.98      (![X3 : $i, X4 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X3)
% 2.74/2.98          | (r2_hidden @ X4 @ X3)
% 2.74/2.98          | ((X4) = (X3))
% 2.74/2.98          | (r2_hidden @ X3 @ X4)
% 2.74/2.98          | ~ (v3_ordinal1 @ X4))),
% 2.74/2.98      inference('cnf', [status(esa)], [t24_ordinal1])).
% 2.74/2.98  thf(t10_wellord2, axiom,
% 2.74/2.98    (![A:$i]:
% 2.74/2.98     ( ( v3_ordinal1 @ A ) =>
% 2.74/2.98       ( ![B:$i]:
% 2.74/2.98         ( ( v3_ordinal1 @ B ) =>
% 2.74/2.98           ( ( r2_hidden @ A @ B ) =>
% 2.74/2.98             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 2.74/2.98  thf('28', plain,
% 2.74/2.98      (![X35 : $i, X36 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X35)
% 2.74/2.98          | ((X36) = (k1_wellord1 @ (k1_wellord2 @ X35) @ X36))
% 2.74/2.98          | ~ (r2_hidden @ X36 @ X35)
% 2.74/2.98          | ~ (v3_ordinal1 @ X36))),
% 2.74/2.98      inference('cnf', [status(esa)], [t10_wellord2])).
% 2.74/2.98  thf('29', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['27', '28'])).
% 2.74/2.98  thf('30', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1))),
% 2.74/2.98      inference('simplify', [status(thm)], ['29'])).
% 2.74/2.98  thf(d1_wellord1, axiom,
% 2.74/2.98    (![A:$i]:
% 2.74/2.98     ( ( v1_relat_1 @ A ) =>
% 2.74/2.98       ( ![B:$i,C:$i]:
% 2.74/2.98         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 2.74/2.98           ( ![D:$i]:
% 2.74/2.98             ( ( r2_hidden @ D @ C ) <=>
% 2.74/2.98               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 2.74/2.98  thf('31', plain,
% 2.74/2.98      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.74/2.98         (((X8) != (k1_wellord1 @ X7 @ X6))
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X9 @ X6) @ X7)
% 2.74/2.98          | ~ (r2_hidden @ X9 @ X8)
% 2.74/2.98          | ~ (v1_relat_1 @ X7))),
% 2.74/2.98      inference('cnf', [status(esa)], [d1_wellord1])).
% 2.74/2.98  thf('32', plain,
% 2.74/2.98      (![X6 : $i, X7 : $i, X9 : $i]:
% 2.74/2.98         (~ (v1_relat_1 @ X7)
% 2.74/2.98          | ~ (r2_hidden @ X9 @ (k1_wellord1 @ X7 @ X6))
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X9 @ X6) @ X7))),
% 2.74/2.98      inference('simplify', [status(thm)], ['31'])).
% 2.74/2.98  thf('33', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X2 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ (k1_wellord2 @ X1))
% 2.74/2.98          | ~ (v1_relat_1 @ (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['30', '32'])).
% 2.74/2.98  thf('34', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('35', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X2 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('demod', [status(thm)], ['33', '34'])).
% 2.74/2.98  thf('36', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         ((r1_tarski @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ 
% 2.74/2.98             (k4_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0) @ 
% 2.74/2.98             (k1_wellord2 @ X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | ((X0) = (X2))
% 2.74/2.98          | (r2_hidden @ X2 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['26', '35'])).
% 2.74/2.98  thf('37', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         ((r2_hidden @ X2 @ X0)
% 2.74/2.98          | ((X0) = (X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | (r2_hidden @ 
% 2.74/2.98             (k4_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0) @ 
% 2.74/2.98             (k1_wellord2 @ X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r1_tarski @ X0 @ X1))),
% 2.74/2.98      inference('simplify', [status(thm)], ['36'])).
% 2.74/2.98  thf('38', plain,
% 2.74/2.98      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X15 @ X16)
% 2.74/2.98          | ~ (r2_hidden @ (k4_tarski @ X17 @ X15) @ X18)
% 2.74/2.98          | (r2_hidden @ X17 @ X16)
% 2.74/2.98          | ~ (zip_tseitin_1 @ X15 @ X18 @ X16))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.74/2.98  thf('39', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.74/2.98         ((r1_tarski @ X1 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X3)
% 2.74/2.98          | (r2_hidden @ (sk_C_2 @ X2 @ (k1_wellord2 @ X1)) @ X3)
% 2.74/2.98          | ~ (r2_hidden @ X1 @ X3))),
% 2.74/2.98      inference('sup-', [status(thm)], ['37', '38'])).
% 2.74/2.98  thf('40', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (r2_hidden @ X1 @ X0)
% 2.74/2.98          | (r2_hidden @ (sk_C_2 @ X2 @ (k1_wellord2 @ X1)) @ X0)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r1_tarski @ X1 @ X2))),
% 2.74/2.98      inference('sup-', [status(thm)], ['18', '39'])).
% 2.74/2.98  thf('41', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         ((r1_tarski @ X1 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | (r2_hidden @ (sk_C_2 @ X2 @ (k1_wellord2 @ X1)) @ X0)
% 2.74/2.98          | ~ (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('simplify', [status(thm)], ['40'])).
% 2.74/2.98  thf('42', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ (sk_C_2 @ X2 @ (k1_wellord2 @ X1)) @ X0)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r1_tarski @ X1 @ X2))),
% 2.74/2.98      inference('sup-', [status(thm)], ['17', '41'])).
% 2.74/2.98  thf('43', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         ((r1_tarski @ X1 @ X2)
% 2.74/2.98          | (r2_hidden @ (sk_C_2 @ X2 @ (k1_wellord2 @ X1)) @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1))),
% 2.74/2.98      inference('simplify', [status(thm)], ['42'])).
% 2.74/2.98  thf('44', plain,
% 2.74/2.98      (![X24 : $i, X25 : $i]:
% 2.74/2.98         (~ (v2_wellord1 @ X24)
% 2.74/2.98          | ~ (r2_hidden @ (sk_C_2 @ X25 @ X24) @ X25)
% 2.74/2.98          | (r1_tarski @ (k3_relat_1 @ X24) @ X25)
% 2.74/2.98          | ~ (v1_relat_1 @ X24))),
% 2.74/2.98      inference('cnf', [status(esa)], [t41_wellord1])).
% 2.74/2.98  thf('45', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r1_tarski @ X1 @ X0)
% 2.74/2.98          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 2.74/2.98          | (r1_tarski @ (k3_relat_1 @ (k1_wellord2 @ X1)) @ X0)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['43', '44'])).
% 2.74/2.98  thf('46', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('47', plain, (![X30 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30))),
% 2.74/2.98      inference('demod', [status(thm)], ['4', '5'])).
% 2.74/2.98  thf('48', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r1_tarski @ X1 @ X0)
% 2.74/2.98          | (r1_tarski @ X1 @ X0)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('demod', [status(thm)], ['45', '46', '47'])).
% 2.74/2.98  thf('49', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 2.74/2.98          | (r1_tarski @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1))),
% 2.74/2.98      inference('simplify', [status(thm)], ['48'])).
% 2.74/2.98  thf('50', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r1_tarski @ X0 @ X1))),
% 2.74/2.98      inference('sup-', [status(thm)], ['16', '49'])).
% 2.74/2.98  thf('51', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         ((r1_tarski @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('simplify', [status(thm)], ['50'])).
% 2.74/2.98  thf('52', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X2 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('demod', [status(thm)], ['33', '34'])).
% 2.74/2.98  thf('53', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r1_tarski @ X0 @ X1)
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | ((X0) = (X2))
% 2.74/2.98          | (r2_hidden @ X2 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['51', '52'])).
% 2.74/2.98  thf('54', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         ((r2_hidden @ X2 @ X0)
% 2.74/2.98          | ((X0) = (X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k1_wellord2 @ X2))
% 2.74/2.98          | (r1_tarski @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('simplify', [status(thm)], ['53'])).
% 2.74/2.98  thf('55', plain,
% 2.74/2.98      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X15 @ X16)
% 2.74/2.98          | ~ (r2_hidden @ (k4_tarski @ X17 @ X15) @ X18)
% 2.74/2.98          | (r2_hidden @ X17 @ X16)
% 2.74/2.98          | ~ (zip_tseitin_1 @ X15 @ X18 @ X16))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.74/2.98  thf('56', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X1) = (X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | (r1_tarski @ X1 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X3)
% 2.74/2.98          | (r2_hidden @ X2 @ X3)
% 2.74/2.98          | ~ (r2_hidden @ X1 @ X3))),
% 2.74/2.98      inference('sup-', [status(thm)], ['54', '55'])).
% 2.74/2.98  thf('57', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (r2_hidden @ X1 @ X0)
% 2.74/2.98          | (r2_hidden @ X2 @ X0)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r1_tarski @ X1 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | ((X1) = (X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1))),
% 2.74/2.98      inference('sup-', [status(thm)], ['15', '56'])).
% 2.74/2.98  thf('58', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X1) = (X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | (r1_tarski @ X1 @ X2)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | (r2_hidden @ X2 @ X0)
% 2.74/2.98          | ~ (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('simplify', [status(thm)], ['57'])).
% 2.74/2.98  thf('59', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X2 @ X0)
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r1_tarski @ X1 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | ((X1) = (X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1))),
% 2.74/2.98      inference('sup-', [status(thm)], ['1', '58'])).
% 2.74/2.98  thf('60', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (((X1) = (X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | (r1_tarski @ X1 @ X2)
% 2.74/2.98          | (r2_hidden @ X2 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1))),
% 2.74/2.98      inference('simplify', [status(thm)], ['59'])).
% 2.74/2.98  thf(t8_wellord2, axiom,
% 2.74/2.98    (![A:$i,B:$i]:
% 2.74/2.98     ( ( r1_tarski @ A @ B ) =>
% 2.74/2.98       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 2.74/2.98  thf('61', plain,
% 2.74/2.98      (![X38 : $i, X39 : $i]:
% 2.74/2.98         (((k2_wellord1 @ (k1_wellord2 @ X39) @ X38) = (k1_wellord2 @ X38))
% 2.74/2.98          | ~ (r1_tarski @ X38 @ X39))),
% 2.74/2.98      inference('cnf', [status(esa)], [t8_wellord2])).
% 2.74/2.98  thf('62', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X2 @ X1)
% 2.74/2.98          | ((X1) = (X2))
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | (r2_hidden @ X0 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['60', '61'])).
% 2.74/2.98  thf('63', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         ((r1_tarski @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('simplify', [status(thm)], ['50'])).
% 2.74/2.98  thf('64', plain,
% 2.74/2.98      (![X35 : $i, X36 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X35)
% 2.74/2.98          | ((X36) = (k1_wellord1 @ (k1_wellord2 @ X35) @ X36))
% 2.74/2.98          | ~ (r2_hidden @ X36 @ X35)
% 2.74/2.98          | ~ (v3_ordinal1 @ X36))),
% 2.74/2.98      inference('cnf', [status(esa)], [t10_wellord2])).
% 2.74/2.98  thf('65', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r1_tarski @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['63', '64'])).
% 2.74/2.98  thf('66', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 2.74/2.98          | (r1_tarski @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('simplify', [status(thm)], ['65'])).
% 2.74/2.98  thf('67', plain,
% 2.74/2.98      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.74/2.98         (((X8) != (k1_wellord1 @ X7 @ X6))
% 2.74/2.98          | ((X9) != (X6))
% 2.74/2.98          | ~ (r2_hidden @ X9 @ X8)
% 2.74/2.98          | ~ (v1_relat_1 @ X7))),
% 2.74/2.98      inference('cnf', [status(esa)], [d1_wellord1])).
% 2.74/2.98  thf('68', plain,
% 2.74/2.98      (![X6 : $i, X7 : $i]:
% 2.74/2.98         (~ (v1_relat_1 @ X7) | ~ (r2_hidden @ X6 @ (k1_wellord1 @ X7 @ X6)))),
% 2.74/2.98      inference('simplify', [status(thm)], ['67'])).
% 2.74/2.98  thf('69', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X0 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r1_tarski @ X1 @ X0)
% 2.74/2.98          | ~ (v1_relat_1 @ (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['66', '68'])).
% 2.74/2.98  thf('70', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('71', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X0 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r1_tarski @ X1 @ X0))),
% 2.74/2.98      inference('demod', [status(thm)], ['69', '70'])).
% 2.74/2.98  thf('72', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X2) = (k1_wellord2 @ X2))
% 2.74/2.98          | ((X2) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X2) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | (r1_tarski @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1))),
% 2.74/2.98      inference('sup-', [status(thm)], ['62', '71'])).
% 2.74/2.98  thf('73', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r1_tarski @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | (r2_hidden @ X0 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X2) = (X0))
% 2.74/2.98          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X2) = (k1_wellord2 @ X2)))),
% 2.74/2.98      inference('simplify', [status(thm)], ['72'])).
% 2.74/2.98  thf('74', plain,
% 2.74/2.98      (![X38 : $i, X39 : $i]:
% 2.74/2.98         (((k2_wellord1 @ (k1_wellord2 @ X39) @ X38) = (k1_wellord2 @ X38))
% 2.74/2.98          | ~ (r1_tarski @ X38 @ X39))),
% 2.74/2.98      inference('cnf', [status(esa)], [t8_wellord2])).
% 2.74/2.98  thf('75', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.98         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X2) = (k1_wellord2 @ X2))
% 2.74/2.98          | ((X2) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X0 @ X2)
% 2.74/2.98          | ~ (v3_ordinal1 @ X2)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['73', '74'])).
% 2.74/2.98  thf('76', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (((k1_wellord2 @ X0) != (k1_wellord2 @ X0))
% 2.74/2.98          | ((k2_wellord1 @ (k1_wellord2 @ X1) @ X0) = (k1_wellord2 @ X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X0) = (X1)))),
% 2.74/2.98      inference('eq_fact', [status(thm)], ['75'])).
% 2.74/2.98  thf('77', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((k2_wellord1 @ (k1_wellord2 @ X1) @ X0) = (k1_wellord2 @ X0)))),
% 2.74/2.98      inference('simplify', [status(thm)], ['76'])).
% 2.74/2.98  thf('78', plain,
% 2.74/2.98      (![X3 : $i, X4 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X3)
% 2.74/2.98          | (r2_hidden @ X4 @ X3)
% 2.74/2.98          | ((X4) = (X3))
% 2.74/2.98          | (r2_hidden @ X3 @ X4)
% 2.74/2.98          | ~ (v3_ordinal1 @ X4))),
% 2.74/2.98      inference('cnf', [status(esa)], [t24_ordinal1])).
% 2.74/2.98  thf('79', plain,
% 2.74/2.98      (![X37 : $i]:
% 2.74/2.98         ((v2_wellord1 @ (k1_wellord2 @ X37)) | ~ (v3_ordinal1 @ X37))),
% 2.74/2.98      inference('cnf', [status(esa)], [t7_wellord2])).
% 2.74/2.98  thf(t11_wellord2, conjecture,
% 2.74/2.98    (![A:$i]:
% 2.74/2.98     ( ( v3_ordinal1 @ A ) =>
% 2.74/2.98       ( ![B:$i]:
% 2.74/2.98         ( ( v3_ordinal1 @ B ) =>
% 2.74/2.98           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 2.74/2.98             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.74/2.98  thf(zf_stmt_5, negated_conjecture,
% 2.74/2.98    (~( ![A:$i]:
% 2.74/2.98        ( ( v3_ordinal1 @ A ) =>
% 2.74/2.98          ( ![B:$i]:
% 2.74/2.98            ( ( v3_ordinal1 @ B ) =>
% 2.74/2.98              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 2.74/2.98                ( ( A ) = ( B ) ) ) ) ) ) )),
% 2.74/2.98    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 2.74/2.98  thf('80', plain,
% 2.74/2.98      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('81', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((k2_wellord1 @ (k1_wellord2 @ X1) @ X0) = (k1_wellord2 @ X0)))),
% 2.74/2.98      inference('simplify', [status(thm)], ['76'])).
% 2.74/2.98  thf('82', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X1) = (X0))
% 2.74/2.98          | (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1))),
% 2.74/2.98      inference('simplify', [status(thm)], ['29'])).
% 2.74/2.98  thf(t57_wellord1, axiom,
% 2.74/2.98    (![A:$i]:
% 2.74/2.98     ( ( v1_relat_1 @ A ) =>
% 2.74/2.98       ( ( v2_wellord1 @ A ) =>
% 2.74/2.98         ( ![B:$i]:
% 2.74/2.98           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 2.74/2.98                ( r4_wellord1 @
% 2.74/2.98                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 2.74/2.98  thf('83', plain,
% 2.74/2.98      (![X28 : $i, X29 : $i]:
% 2.74/2.98         (~ (v2_wellord1 @ X28)
% 2.74/2.98          | ~ (r4_wellord1 @ X28 @ 
% 2.74/2.98               (k2_wellord1 @ X28 @ (k1_wellord1 @ X28 @ X29)))
% 2.74/2.98          | ~ (r2_hidden @ X29 @ (k3_relat_1 @ X28))
% 2.74/2.98          | ~ (v1_relat_1 @ X28))),
% 2.74/2.98      inference('cnf', [status(esa)], [t57_wellord1])).
% 2.74/2.98  thf('84', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 2.74/2.98             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 2.74/2.98          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['82', '83'])).
% 2.74/2.98  thf('85', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('86', plain, (![X30 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30))),
% 2.74/2.98      inference('demod', [status(thm)], ['4', '5'])).
% 2.74/2.98  thf('87', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 2.74/2.98             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ~ (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 2.74/2.98      inference('demod', [status(thm)], ['84', '85', '86'])).
% 2.74/2.98  thf('88', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 2.74/2.98          | ~ (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ~ (v3_ordinal1 @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['81', '87'])).
% 2.74/2.98  thf('89', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X0 @ X1)
% 2.74/2.98          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X1)
% 2.74/2.98          | (r2_hidden @ X1 @ X0)
% 2.74/2.98          | ((X0) = (X1))
% 2.74/2.98          | ~ (v3_ordinal1 @ X0)
% 2.74/2.98          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 2.74/2.98      inference('simplify', [status(thm)], ['88'])).
% 2.74/2.98  thf('90', plain,
% 2.74/2.98      ((~ (v3_ordinal1 @ sk_B)
% 2.74/2.98        | ((sk_B) = (sk_A))
% 2.74/2.98        | (r2_hidden @ sk_A @ sk_B)
% 2.74/2.98        | ~ (v3_ordinal1 @ sk_A)
% 2.74/2.98        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 2.74/2.98        | ~ (r2_hidden @ sk_B @ sk_A))),
% 2.74/2.98      inference('sup-', [status(thm)], ['80', '89'])).
% 2.74/2.98  thf('91', plain, ((v3_ordinal1 @ sk_B)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('92', plain, ((v3_ordinal1 @ sk_A)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('93', plain,
% 2.74/2.98      ((((sk_B) = (sk_A))
% 2.74/2.98        | (r2_hidden @ sk_A @ sk_B)
% 2.74/2.98        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 2.74/2.98        | ~ (r2_hidden @ sk_B @ sk_A))),
% 2.74/2.98      inference('demod', [status(thm)], ['90', '91', '92'])).
% 2.74/2.98  thf('94', plain, (((sk_A) != (sk_B))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('95', plain,
% 2.74/2.98      (((r2_hidden @ sk_A @ sk_B)
% 2.74/2.98        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 2.74/2.98        | ~ (r2_hidden @ sk_B @ sk_A))),
% 2.74/2.98      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 2.74/2.98  thf('96', plain,
% 2.74/2.98      ((~ (v3_ordinal1 @ sk_A)
% 2.74/2.98        | ~ (r2_hidden @ sk_B @ sk_A)
% 2.74/2.98        | (r2_hidden @ sk_A @ sk_B))),
% 2.74/2.98      inference('sup-', [status(thm)], ['79', '95'])).
% 2.74/2.98  thf('97', plain, ((v3_ordinal1 @ sk_A)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('98', plain, ((~ (r2_hidden @ sk_B @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 2.74/2.98      inference('demod', [status(thm)], ['96', '97'])).
% 2.74/2.98  thf('99', plain,
% 2.74/2.98      ((~ (v3_ordinal1 @ sk_B)
% 2.74/2.98        | (r2_hidden @ sk_A @ sk_B)
% 2.74/2.98        | ((sk_B) = (sk_A))
% 2.74/2.98        | ~ (v3_ordinal1 @ sk_A)
% 2.74/2.98        | (r2_hidden @ sk_A @ sk_B))),
% 2.74/2.98      inference('sup-', [status(thm)], ['78', '98'])).
% 2.74/2.98  thf('100', plain, ((v3_ordinal1 @ sk_B)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('101', plain, ((v3_ordinal1 @ sk_A)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('102', plain,
% 2.74/2.98      (((r2_hidden @ sk_A @ sk_B)
% 2.74/2.98        | ((sk_B) = (sk_A))
% 2.74/2.98        | (r2_hidden @ sk_A @ sk_B))),
% 2.74/2.98      inference('demod', [status(thm)], ['99', '100', '101'])).
% 2.74/2.98  thf('103', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 2.74/2.98      inference('simplify', [status(thm)], ['102'])).
% 2.74/2.98  thf('104', plain, (((sk_A) != (sk_B))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('105', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.74/2.98      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 2.74/2.98  thf('106', plain,
% 2.74/2.98      (![X35 : $i, X36 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X35)
% 2.74/2.98          | ((X36) = (k1_wellord1 @ (k1_wellord2 @ X35) @ X36))
% 2.74/2.98          | ~ (r2_hidden @ X36 @ X35)
% 2.74/2.98          | ~ (v3_ordinal1 @ X36))),
% 2.74/2.98      inference('cnf', [status(esa)], [t10_wellord2])).
% 2.74/2.98  thf('107', plain,
% 2.74/2.98      ((~ (v3_ordinal1 @ sk_A)
% 2.74/2.98        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 2.74/2.98        | ~ (v3_ordinal1 @ sk_B))),
% 2.74/2.98      inference('sup-', [status(thm)], ['105', '106'])).
% 2.74/2.98  thf('108', plain, ((v3_ordinal1 @ sk_A)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('109', plain, ((v3_ordinal1 @ sk_B)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('110', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 2.74/2.98      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.74/2.98  thf('111', plain,
% 2.74/2.98      (![X28 : $i, X29 : $i]:
% 2.74/2.98         (~ (v2_wellord1 @ X28)
% 2.74/2.98          | ~ (r4_wellord1 @ X28 @ 
% 2.74/2.98               (k2_wellord1 @ X28 @ (k1_wellord1 @ X28 @ X29)))
% 2.74/2.98          | ~ (r2_hidden @ X29 @ (k3_relat_1 @ X28))
% 2.74/2.98          | ~ (v1_relat_1 @ X28))),
% 2.74/2.98      inference('cnf', [status(esa)], [t57_wellord1])).
% 2.74/2.98  thf('112', plain,
% 2.74/2.98      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 2.74/2.98           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 2.74/2.98        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 2.74/2.98        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 2.74/2.98        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['110', '111'])).
% 2.74/2.98  thf('113', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('114', plain,
% 2.74/2.98      (![X30 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30))),
% 2.74/2.98      inference('demod', [status(thm)], ['4', '5'])).
% 2.74/2.98  thf('115', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.74/2.98      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 2.74/2.98  thf('116', plain,
% 2.74/2.98      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 2.74/2.98           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 2.74/2.98        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 2.74/2.98      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 2.74/2.98  thf('117', plain,
% 2.74/2.98      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 2.74/2.98        | ~ (v3_ordinal1 @ sk_A)
% 2.74/2.98        | ((sk_A) = (sk_B))
% 2.74/2.98        | (r2_hidden @ sk_B @ sk_A)
% 2.74/2.98        | ~ (v3_ordinal1 @ sk_B)
% 2.74/2.98        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['77', '116'])).
% 2.74/2.98  thf('118', plain,
% 2.74/2.98      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf(t50_wellord1, axiom,
% 2.74/2.98    (![A:$i]:
% 2.74/2.98     ( ( v1_relat_1 @ A ) =>
% 2.74/2.98       ( ![B:$i]:
% 2.74/2.98         ( ( v1_relat_1 @ B ) =>
% 2.74/2.98           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 2.74/2.98  thf('119', plain,
% 2.74/2.98      (![X26 : $i, X27 : $i]:
% 2.74/2.98         (~ (v1_relat_1 @ X26)
% 2.74/2.98          | (r4_wellord1 @ X26 @ X27)
% 2.74/2.98          | ~ (r4_wellord1 @ X27 @ X26)
% 2.74/2.98          | ~ (v1_relat_1 @ X27))),
% 2.74/2.98      inference('cnf', [status(esa)], [t50_wellord1])).
% 2.74/2.98  thf('120', plain,
% 2.74/2.98      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 2.74/2.98        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 2.74/2.98        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['118', '119'])).
% 2.74/2.98  thf('121', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('122', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('123', plain,
% 2.74/2.98      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 2.74/2.98      inference('demod', [status(thm)], ['120', '121', '122'])).
% 2.74/2.98  thf('124', plain, ((v3_ordinal1 @ sk_A)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('125', plain, ((v3_ordinal1 @ sk_B)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('126', plain,
% 2.74/2.98      ((((sk_A) = (sk_B))
% 2.74/2.98        | (r2_hidden @ sk_B @ sk_A)
% 2.74/2.98        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 2.74/2.98      inference('demod', [status(thm)], ['117', '123', '124', '125'])).
% 2.74/2.98  thf('127', plain, (((sk_A) != (sk_B))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('128', plain,
% 2.74/2.98      (((r2_hidden @ sk_B @ sk_A) | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 2.74/2.98      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 2.74/2.98  thf('129', plain, ((~ (v3_ordinal1 @ sk_B) | (r2_hidden @ sk_B @ sk_A))),
% 2.74/2.98      inference('sup-', [status(thm)], ['0', '128'])).
% 2.74/2.98  thf('130', plain, ((v3_ordinal1 @ sk_B)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('131', plain, ((r2_hidden @ sk_B @ sk_A)),
% 2.74/2.98      inference('demod', [status(thm)], ['129', '130'])).
% 2.74/2.98  thf('132', plain,
% 2.74/2.98      (![X35 : $i, X36 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X35)
% 2.74/2.98          | ((X36) = (k1_wellord1 @ (k1_wellord2 @ X35) @ X36))
% 2.74/2.98          | ~ (r2_hidden @ X36 @ X35)
% 2.74/2.98          | ~ (v3_ordinal1 @ X36))),
% 2.74/2.98      inference('cnf', [status(esa)], [t10_wellord2])).
% 2.74/2.98  thf('133', plain,
% 2.74/2.98      ((~ (v3_ordinal1 @ sk_B)
% 2.74/2.98        | ((sk_B) = (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B))
% 2.74/2.98        | ~ (v3_ordinal1 @ sk_A))),
% 2.74/2.98      inference('sup-', [status(thm)], ['131', '132'])).
% 2.74/2.98  thf('134', plain, ((v3_ordinal1 @ sk_B)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('135', plain, ((v3_ordinal1 @ sk_A)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('136', plain, (((sk_B) = (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B))),
% 2.74/2.98      inference('demod', [status(thm)], ['133', '134', '135'])).
% 2.74/2.98  thf('137', plain,
% 2.74/2.98      (![X6 : $i, X7 : $i]:
% 2.74/2.98         (~ (v1_relat_1 @ X7) | ~ (r2_hidden @ X6 @ (k1_wellord1 @ X7 @ X6)))),
% 2.74/2.98      inference('simplify', [status(thm)], ['67'])).
% 2.74/2.98  thf('138', plain,
% 2.74/2.98      ((~ (r2_hidden @ sk_B @ sk_B) | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['136', '137'])).
% 2.74/2.98  thf('139', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('140', plain, (~ (r2_hidden @ sk_B @ sk_B)),
% 2.74/2.98      inference('demod', [status(thm)], ['138', '139'])).
% 2.74/2.98  thf('141', plain,
% 2.74/2.98      (![X0 : $i, X1 : $i]:
% 2.74/2.98         (~ (v3_ordinal1 @ X0) | (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['2', '14'])).
% 2.74/2.98  thf('142', plain, ((r2_hidden @ sk_B @ sk_A)),
% 2.74/2.98      inference('demod', [status(thm)], ['129', '130'])).
% 2.74/2.98  thf('143', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 2.74/2.98      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.74/2.98  thf('144', plain,
% 2.74/2.98      (![X6 : $i, X7 : $i, X9 : $i]:
% 2.74/2.98         (~ (v1_relat_1 @ X7)
% 2.74/2.98          | ~ (r2_hidden @ X9 @ (k1_wellord1 @ X7 @ X6))
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X9 @ X6) @ X7))),
% 2.74/2.98      inference('simplify', [status(thm)], ['31'])).
% 2.74/2.98  thf('145', plain,
% 2.74/2.98      (![X0 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X0 @ sk_A)
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ (k1_wellord2 @ sk_B))
% 2.74/2.98          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 2.74/2.98      inference('sup-', [status(thm)], ['143', '144'])).
% 2.74/2.98  thf('146', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 2.74/2.98      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 2.74/2.98  thf('147', plain,
% 2.74/2.98      (![X0 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X0 @ sk_A)
% 2.74/2.98          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ (k1_wellord2 @ sk_B)))),
% 2.74/2.98      inference('demod', [status(thm)], ['145', '146'])).
% 2.74/2.98  thf('148', plain,
% 2.74/2.98      ((r2_hidden @ (k4_tarski @ sk_B @ sk_A) @ (k1_wellord2 @ sk_B))),
% 2.74/2.98      inference('sup-', [status(thm)], ['142', '147'])).
% 2.74/2.98  thf('149', plain,
% 2.74/2.98      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 2.74/2.98         (~ (r2_hidden @ X15 @ X16)
% 2.74/2.98          | ~ (r2_hidden @ (k4_tarski @ X17 @ X15) @ X18)
% 2.74/2.98          | (r2_hidden @ X17 @ X16)
% 2.74/2.98          | ~ (zip_tseitin_1 @ X15 @ X18 @ X16))),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.74/2.98  thf('150', plain,
% 2.74/2.98      (![X0 : $i]:
% 2.74/2.98         (~ (zip_tseitin_1 @ sk_A @ (k1_wellord2 @ sk_B) @ X0)
% 2.74/2.98          | (r2_hidden @ sk_B @ X0)
% 2.74/2.98          | ~ (r2_hidden @ sk_A @ X0))),
% 2.74/2.98      inference('sup-', [status(thm)], ['148', '149'])).
% 2.74/2.98  thf('151', plain,
% 2.74/2.98      ((~ (v3_ordinal1 @ sk_B)
% 2.74/2.98        | ~ (r2_hidden @ sk_A @ sk_B)
% 2.74/2.98        | (r2_hidden @ sk_B @ sk_B))),
% 2.74/2.98      inference('sup-', [status(thm)], ['141', '150'])).
% 2.74/2.98  thf('152', plain, ((v3_ordinal1 @ sk_B)),
% 2.74/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.74/2.98  thf('153', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.74/2.98      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 2.74/2.98  thf('154', plain, ((r2_hidden @ sk_B @ sk_B)),
% 2.74/2.98      inference('demod', [status(thm)], ['151', '152', '153'])).
% 2.74/2.98  thf('155', plain, ($false), inference('demod', [status(thm)], ['140', '154'])).
% 2.74/2.98  
% 2.74/2.98  % SZS output end Refutation
% 2.74/2.98  
% 2.74/2.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
