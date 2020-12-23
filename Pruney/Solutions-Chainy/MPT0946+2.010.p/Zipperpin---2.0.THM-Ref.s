%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0cJrcOBPVL

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:29 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  202 (1280 expanded)
%              Number of leaves         :   34 ( 390 expanded)
%              Depth                    :   55
%              Number of atoms          : 1876 (13656 expanded)
%              Number of equality atoms :   71 ( 671 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X39: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('2',plain,(
    ! [X39: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( X38
        = ( k1_wellord1 @ ( k1_wellord2 @ X37 ) @ X38 ) )
      | ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ( X8 = X7 )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('8',plain,(
    ! [X39: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('9',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ A )
       => ! [D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B )
           => ( r2_hidden @ D @ A ) ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_1 @ X19 @ X22 @ X23 )
      | ( r2_hidden @ X19 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( X38
        = ( k1_wellord1 @ ( k1_wellord2 @ X37 ) @ X38 ) )
      | ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_1 @ X19 @ X22 @ X23 )
      | ( r2_hidden @ X19 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X39: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X39 ) )
      | ~ ( v3_ordinal1 @ X39 ) ) ),
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

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
       != ( k1_wellord2 @ X32 ) )
      | ( ( k3_relat_1 @ X33 )
        = X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('16',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X32 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
        = X32 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('17',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('18',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k3_relat_1 @ B ) )
        & ( A
          = ( k1_wellord1 @ B @ C ) ) ) ) )).

thf(zf_stmt_5,axiom,(
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

thf('19',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( v2_wellord1 @ X24 )
      | ~ ( r1_tarski @ X25 @ ( k3_relat_1 @ X24 ) )
      | ( X25
       != ( k3_relat_1 @ X24 ) )
      | ( zip_tseitin_1 @ X27 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,(
    ! [X24: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( zip_tseitin_1 @ X27 @ X24 @ ( k3_relat_1 @ X24 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X24 ) @ ( k3_relat_1 @ X24 ) )
      | ~ ( v2_wellord1 @ X24 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X24: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( zip_tseitin_1 @ X27 @ X24 @ ( k3_relat_1 @ X24 ) )
      | ~ ( v2_wellord1 @ X24 ) ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X22 )
      | ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_1 @ X19 @ X22 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( zip_tseitin_1 @ X1 @ X0 @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 )
      | ( zip_tseitin_1 @ X1 @ X2 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X2 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('41',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X41 ) @ X40 )
        = ( k1_wellord2 @ X40 ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ X2 @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
        = ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_wellord1 @ X30 )
      | ~ ( r4_wellord1 @ X30 @ ( k2_wellord1 @ X30 @ ( k1_wellord1 @ X30 @ X31 ) ) )
      | ~ ( r2_hidden @ X31 @ ( k3_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('46',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X3 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( zip_tseitin_1 @ X0 @ X3 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( zip_tseitin_1 @ sk_B @ X0 @ sk_A )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ sk_B @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_B @ X0 @ sk_A )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ sk_B @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ sk_A )
      | ( zip_tseitin_1 @ sk_B @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ sk_B @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_B @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ sk_B @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(condensation,[status(thm)],['56'])).

thf('58',plain,(
    ! [X19: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_1 @ X19 @ X22 @ X23 )
      | ( r2_hidden @ X19 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_B @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( zip_tseitin_1 @ X1 @ X0 @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord1 @ X0 @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ sk_B ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( sk_B = sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','61'])).

thf('63',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_B = sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ sk_B ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X41 ) @ X40 )
        = ( k1_wellord2 @ X40 ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord1 @ X0 @ sk_B ) )
        = ( k1_wellord2 @ ( k1_wellord1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_wellord1 @ X30 )
      | ~ ( r4_wellord1 @ X30 @ ( k2_wellord1 @ X30 @ ( k1_wellord1 @ X30 @ X31 ) ) )
      | ~ ( r2_hidden @ X31 @ ( k3_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('74',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ ( k1_wellord2 @ sk_A ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('76',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('77',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('78',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','78'])).

thf('80',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','86'])).

thf('88',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','89'])).

thf('91',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( X38
        = ( k1_wellord1 @ ( k1_wellord2 @ X37 ) @ X38 ) )
      | ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('98',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_wellord1 @ X30 )
      | ~ ( r4_wellord1 @ X30 @ ( k2_wellord1 @ X30 @ ( k1_wellord1 @ X30 @ X31 ) ) )
      | ~ ( r2_hidden @ X31 @ ( k3_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('103',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('105',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('106',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('107',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('109',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('111',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('113',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ X0 ) @ ( k1_wellord2 @ X2 ) )
      | ~ ( v3_ordinal1 @ X2 )
      | ( X0 = X2 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X22 )
      | ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_1 @ X19 @ X22 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( zip_tseitin_1 @ X1 @ ( k1_wellord2 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','121'])).

thf('123',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('129',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('132',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_A ) @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X19 ) @ X22 )
      | ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_1 @ X19 @ X22 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( zip_tseitin_1 @ sk_A @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['108','138'])).

thf('140',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('142',plain,
    ( ( r2_hidden @ sk_B @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['129'])).

thf('144',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v3_ordinal1 @ X37 )
      | ( X38
        = ( k1_wellord1 @ ( k1_wellord2 @ X37 ) @ X38 ) )
      | ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( v3_ordinal1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('145',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k1_wellord1 @ X11 @ X10 ) )
      | ( X13 != X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('150',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_wellord1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('153',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['142','153'])).

thf('155',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X41 ) @ X40 )
        = ( k1_wellord2 @ X40 ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('156',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('158',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( r4_wellord1 @ X28 @ X29 )
      | ~ ( r4_wellord1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('161',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('162',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','156','162'])).

thf('164',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','163'])).

thf('165',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['164','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0cJrcOBPVL
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:27 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.53/1.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.53/1.77  % Solved by: fo/fo7.sh
% 1.53/1.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.77  % done 595 iterations in 1.304s
% 1.53/1.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.53/1.77  % SZS output start Refutation
% 1.53/1.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.53/1.77  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 1.53/1.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.53/1.77  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.53/1.77  thf(sk_B_type, type, sk_B: $i).
% 1.53/1.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.53/1.77  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.53/1.77  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 1.53/1.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 1.53/1.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.53/1.77  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 1.53/1.77  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 1.53/1.77  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.77  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.53/1.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.53/1.77  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 1.53/1.77  thf(t7_wellord2, axiom,
% 1.53/1.77    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 1.53/1.77  thf('0', plain,
% 1.53/1.77      (![X39 : $i]:
% 1.53/1.77         ((v2_wellord1 @ (k1_wellord2 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 1.53/1.77      inference('cnf', [status(esa)], [t7_wellord2])).
% 1.53/1.77  thf(t24_ordinal1, axiom,
% 1.53/1.77    (![A:$i]:
% 1.53/1.77     ( ( v3_ordinal1 @ A ) =>
% 1.53/1.77       ( ![B:$i]:
% 1.53/1.77         ( ( v3_ordinal1 @ B ) =>
% 1.53/1.77           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 1.53/1.77                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 1.53/1.77  thf('1', plain,
% 1.53/1.77      (![X7 : $i, X8 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X7)
% 1.53/1.77          | (r2_hidden @ X8 @ X7)
% 1.53/1.77          | ((X8) = (X7))
% 1.53/1.77          | (r2_hidden @ X7 @ X8)
% 1.53/1.77          | ~ (v3_ordinal1 @ X8))),
% 1.53/1.77      inference('cnf', [status(esa)], [t24_ordinal1])).
% 1.53/1.77  thf('2', plain,
% 1.53/1.77      (![X39 : $i]:
% 1.53/1.77         ((v2_wellord1 @ (k1_wellord2 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 1.53/1.77      inference('cnf', [status(esa)], [t7_wellord2])).
% 1.53/1.77  thf('3', plain,
% 1.53/1.77      (![X7 : $i, X8 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X7)
% 1.53/1.77          | (r2_hidden @ X8 @ X7)
% 1.53/1.77          | ((X8) = (X7))
% 1.53/1.77          | (r2_hidden @ X7 @ X8)
% 1.53/1.77          | ~ (v3_ordinal1 @ X8))),
% 1.53/1.77      inference('cnf', [status(esa)], [t24_ordinal1])).
% 1.53/1.77  thf(t10_wellord2, axiom,
% 1.53/1.77    (![A:$i]:
% 1.53/1.77     ( ( v3_ordinal1 @ A ) =>
% 1.53/1.77       ( ![B:$i]:
% 1.53/1.77         ( ( v3_ordinal1 @ B ) =>
% 1.53/1.77           ( ( r2_hidden @ A @ B ) =>
% 1.53/1.77             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 1.53/1.77  thf('4', plain,
% 1.53/1.77      (![X37 : $i, X38 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X37)
% 1.53/1.77          | ((X38) = (k1_wellord1 @ (k1_wellord2 @ X37) @ X38))
% 1.53/1.77          | ~ (r2_hidden @ X38 @ X37)
% 1.53/1.77          | ~ (v3_ordinal1 @ X38))),
% 1.53/1.77      inference('cnf', [status(esa)], [t10_wellord2])).
% 1.53/1.77  thf('5', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X1)
% 1.53/1.77          | (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ((X1) = (X0))
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 1.53/1.77          | ~ (v3_ordinal1 @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['3', '4'])).
% 1.53/1.77  thf('6', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | ((X1) = (X0))
% 1.53/1.77          | (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1))),
% 1.53/1.77      inference('simplify', [status(thm)], ['5'])).
% 1.53/1.77  thf('7', plain,
% 1.53/1.77      (![X7 : $i, X8 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X7)
% 1.53/1.77          | (r2_hidden @ X8 @ X7)
% 1.53/1.77          | ((X8) = (X7))
% 1.53/1.77          | (r2_hidden @ X7 @ X8)
% 1.53/1.77          | ~ (v3_ordinal1 @ X8))),
% 1.53/1.77      inference('cnf', [status(esa)], [t24_ordinal1])).
% 1.53/1.77  thf('8', plain,
% 1.53/1.77      (![X39 : $i]:
% 1.53/1.77         ((v2_wellord1 @ (k1_wellord2 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 1.53/1.77      inference('cnf', [status(esa)], [t7_wellord2])).
% 1.53/1.77  thf(t11_wellord2, conjecture,
% 1.53/1.77    (![A:$i]:
% 1.53/1.77     ( ( v3_ordinal1 @ A ) =>
% 1.53/1.77       ( ![B:$i]:
% 1.53/1.77         ( ( v3_ordinal1 @ B ) =>
% 1.53/1.77           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 1.53/1.77             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.53/1.77  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.77    (~( ![A:$i]:
% 1.53/1.77        ( ( v3_ordinal1 @ A ) =>
% 1.53/1.77          ( ![B:$i]:
% 1.53/1.77            ( ( v3_ordinal1 @ B ) =>
% 1.53/1.77              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 1.53/1.77                ( ( A ) = ( B ) ) ) ) ) ) )),
% 1.53/1.77    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 1.53/1.77  thf('9', plain,
% 1.53/1.77      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf(t36_wellord1, axiom,
% 1.53/1.77    (![A:$i,B:$i]:
% 1.53/1.77     ( ( v1_relat_1 @ B ) =>
% 1.53/1.77       ( ( ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) & ( v2_wellord1 @ B ) ) =>
% 1.53/1.77         ( ( ~( ( ![C:$i]:
% 1.53/1.77                  ( ~( ( ( A ) = ( k1_wellord1 @ B @ C ) ) & 
% 1.53/1.77                       ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) ) ) ) & 
% 1.53/1.77                ( ( A ) != ( k3_relat_1 @ B ) ) ) ) <=>
% 1.53/1.77           ( ![C:$i]:
% 1.53/1.77             ( ( r2_hidden @ C @ A ) =>
% 1.53/1.77               ( ![D:$i]:
% 1.53/1.77                 ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) =>
% 1.53/1.77                   ( r2_hidden @ D @ A ) ) ) ) ) ) ) ))).
% 1.53/1.77  thf(zf_stmt_1, axiom,
% 1.53/1.77    (![C:$i,B:$i,A:$i]:
% 1.53/1.77     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 1.53/1.77       ( ( r2_hidden @ C @ A ) =>
% 1.53/1.77         ( ![D:$i]:
% 1.53/1.77           ( ( r2_hidden @ ( k4_tarski @ D @ C ) @ B ) => ( r2_hidden @ D @ A ) ) ) ) ))).
% 1.53/1.77  thf('10', plain,
% 1.53/1.77      (![X19 : $i, X22 : $i, X23 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X19 @ X22 @ X23) | (r2_hidden @ X19 @ X23))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.53/1.77  thf('11', plain,
% 1.53/1.77      (![X37 : $i, X38 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X37)
% 1.53/1.77          | ((X38) = (k1_wellord1 @ (k1_wellord2 @ X37) @ X38))
% 1.53/1.77          | ~ (r2_hidden @ X38 @ X37)
% 1.53/1.77          | ~ (v3_ordinal1 @ X38))),
% 1.53/1.77      inference('cnf', [status(esa)], [t10_wellord2])).
% 1.53/1.77  thf('12', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X1 @ X2 @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 1.53/1.77          | ~ (v3_ordinal1 @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['10', '11'])).
% 1.53/1.77  thf('13', plain,
% 1.53/1.77      (![X19 : $i, X22 : $i, X23 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X19 @ X22 @ X23) | (r2_hidden @ X19 @ X23))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.53/1.77  thf('14', plain,
% 1.53/1.77      (![X39 : $i]:
% 1.53/1.77         ((v2_wellord1 @ (k1_wellord2 @ X39)) | ~ (v3_ordinal1 @ X39))),
% 1.53/1.77      inference('cnf', [status(esa)], [t7_wellord2])).
% 1.53/1.77  thf(d1_wellord2, axiom,
% 1.53/1.77    (![A:$i,B:$i]:
% 1.53/1.77     ( ( v1_relat_1 @ B ) =>
% 1.53/1.77       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 1.53/1.77         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 1.53/1.77           ( ![C:$i,D:$i]:
% 1.53/1.77             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 1.53/1.77               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 1.53/1.77                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 1.53/1.77  thf('15', plain,
% 1.53/1.77      (![X32 : $i, X33 : $i]:
% 1.53/1.77         (((X33) != (k1_wellord2 @ X32))
% 1.53/1.77          | ((k3_relat_1 @ X33) = (X32))
% 1.53/1.77          | ~ (v1_relat_1 @ X33))),
% 1.53/1.77      inference('cnf', [status(esa)], [d1_wellord2])).
% 1.53/1.77  thf('16', plain,
% 1.53/1.77      (![X32 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ (k1_wellord2 @ X32))
% 1.53/1.77          | ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32)))),
% 1.53/1.77      inference('simplify', [status(thm)], ['15'])).
% 1.53/1.77  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 1.53/1.77  thf('17', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('18', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 1.53/1.77      inference('demod', [status(thm)], ['16', '17'])).
% 1.53/1.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.53/1.77  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 1.53/1.77  thf(zf_stmt_4, axiom,
% 1.53/1.77    (![C:$i,B:$i,A:$i]:
% 1.53/1.77     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 1.53/1.77       ( ( r2_hidden @ C @ ( k3_relat_1 @ B ) ) & 
% 1.53/1.77         ( ( A ) = ( k1_wellord1 @ B @ C ) ) ) ))).
% 1.53/1.77  thf(zf_stmt_5, axiom,
% 1.53/1.77    (![A:$i,B:$i]:
% 1.53/1.77     ( ( v1_relat_1 @ B ) =>
% 1.53/1.77       ( ( ( v2_wellord1 @ B ) & ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) ) =>
% 1.53/1.77         ( ( ~( ( ( A ) != ( k3_relat_1 @ B ) ) & 
% 1.53/1.77                ( ![C:$i]: ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ) ) <=>
% 1.53/1.77           ( ![C:$i]: ( zip_tseitin_1 @ C @ B @ A ) ) ) ) ))).
% 1.53/1.77  thf('19', plain,
% 1.53/1.77      (![X24 : $i, X25 : $i, X27 : $i]:
% 1.53/1.77         (~ (v2_wellord1 @ X24)
% 1.53/1.77          | ~ (r1_tarski @ X25 @ (k3_relat_1 @ X24))
% 1.53/1.77          | ((X25) != (k3_relat_1 @ X24))
% 1.53/1.77          | (zip_tseitin_1 @ X27 @ X24 @ X25)
% 1.53/1.77          | ~ (v1_relat_1 @ X24))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.53/1.77  thf('20', plain,
% 1.53/1.77      (![X24 : $i, X27 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X24)
% 1.53/1.77          | (zip_tseitin_1 @ X27 @ X24 @ (k3_relat_1 @ X24))
% 1.53/1.77          | ~ (r1_tarski @ (k3_relat_1 @ X24) @ (k3_relat_1 @ X24))
% 1.53/1.77          | ~ (v2_wellord1 @ X24))),
% 1.53/1.77      inference('simplify', [status(thm)], ['19'])).
% 1.53/1.77  thf(d10_xboole_0, axiom,
% 1.53/1.77    (![A:$i,B:$i]:
% 1.53/1.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.53/1.77  thf('21', plain,
% 1.53/1.77      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.53/1.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.53/1.77  thf('22', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.53/1.77      inference('simplify', [status(thm)], ['21'])).
% 1.53/1.77  thf('23', plain,
% 1.53/1.77      (![X24 : $i, X27 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X24)
% 1.53/1.77          | (zip_tseitin_1 @ X27 @ X24 @ (k3_relat_1 @ X24))
% 1.53/1.77          | ~ (v2_wellord1 @ X24))),
% 1.53/1.77      inference('demod', [status(thm)], ['20', '22'])).
% 1.53/1.77  thf('24', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0)
% 1.53/1.77          | ~ (v2_wellord1 @ (k1_wellord2 @ X0))
% 1.53/1.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 1.53/1.77      inference('sup+', [status(thm)], ['18', '23'])).
% 1.53/1.77  thf('25', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('26', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0)
% 1.53/1.77          | ~ (v2_wellord1 @ (k1_wellord2 @ X0)))),
% 1.53/1.77      inference('demod', [status(thm)], ['24', '25'])).
% 1.53/1.77  thf('27', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X0) | (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['14', '26'])).
% 1.53/1.77  thf(d3_tarski, axiom,
% 1.53/1.77    (![A:$i,B:$i]:
% 1.53/1.77     ( ( r1_tarski @ A @ B ) <=>
% 1.53/1.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.53/1.77  thf('28', plain,
% 1.53/1.77      (![X1 : $i, X3 : $i]:
% 1.53/1.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.53/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.53/1.77  thf(d1_wellord1, axiom,
% 1.53/1.77    (![A:$i]:
% 1.53/1.77     ( ( v1_relat_1 @ A ) =>
% 1.53/1.77       ( ![B:$i,C:$i]:
% 1.53/1.77         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 1.53/1.77           ( ![D:$i]:
% 1.53/1.77             ( ( r2_hidden @ D @ C ) <=>
% 1.53/1.77               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 1.53/1.77  thf('29', plain,
% 1.53/1.77      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.53/1.77         (((X12) != (k1_wellord1 @ X11 @ X10))
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11)
% 1.53/1.77          | ~ (r2_hidden @ X13 @ X12)
% 1.53/1.77          | ~ (v1_relat_1 @ X11))),
% 1.53/1.77      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.53/1.77  thf('30', plain,
% 1.53/1.77      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X11)
% 1.53/1.77          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X11 @ X10))
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11))),
% 1.53/1.77      inference('simplify', [status(thm)], ['29'])).
% 1.53/1.77  thf('31', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 1.53/1.77          | (r2_hidden @ 
% 1.53/1.77             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 1.53/1.77          | ~ (v1_relat_1 @ X1))),
% 1.53/1.77      inference('sup-', [status(thm)], ['28', '30'])).
% 1.53/1.77  thf('32', plain,
% 1.53/1.77      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.77         (~ (r2_hidden @ X19 @ X20)
% 1.53/1.77          | ~ (r2_hidden @ (k4_tarski @ X21 @ X19) @ X22)
% 1.53/1.77          | (r2_hidden @ X21 @ X20)
% 1.53/1.77          | ~ (zip_tseitin_1 @ X19 @ X22 @ X20))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.53/1.77  thf('33', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.53/1.77          | ~ (zip_tseitin_1 @ X1 @ X0 @ X3)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3)
% 1.53/1.77          | ~ (r2_hidden @ X1 @ X3))),
% 1.53/1.77      inference('sup-', [status(thm)], ['31', '32'])).
% 1.53/1.77  thf('34', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X0)
% 1.53/1.77          | ~ (r2_hidden @ X1 @ X0)
% 1.53/1.77          | (r2_hidden @ 
% 1.53/1.77             (sk_C @ X2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1)) @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X2)
% 1.53/1.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['27', '33'])).
% 1.53/1.77  thf('35', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('36', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X0)
% 1.53/1.77          | ~ (r2_hidden @ X1 @ X0)
% 1.53/1.77          | (r2_hidden @ 
% 1.53/1.77             (sk_C @ X2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1)) @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X2))),
% 1.53/1.77      inference('demod', [status(thm)], ['34', '35'])).
% 1.53/1.77  thf('37', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X1 @ X3 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X2)
% 1.53/1.77          | (r2_hidden @ 
% 1.53/1.77             (sk_C @ X2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1)) @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['13', '36'])).
% 1.53/1.77  thf('38', plain,
% 1.53/1.77      (![X1 : $i, X3 : $i]:
% 1.53/1.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.53/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.53/1.77  thf('39', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0)
% 1.53/1.77          | (zip_tseitin_1 @ X1 @ X2 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['37', '38'])).
% 1.53/1.77  thf('40', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X1 @ X2 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1) @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0))),
% 1.53/1.77      inference('simplify', [status(thm)], ['39'])).
% 1.53/1.77  thf(t8_wellord2, axiom,
% 1.53/1.77    (![A:$i,B:$i]:
% 1.53/1.77     ( ( r1_tarski @ A @ B ) =>
% 1.53/1.77       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 1.53/1.77  thf('41', plain,
% 1.53/1.77      (![X40 : $i, X41 : $i]:
% 1.53/1.77         (((k2_wellord1 @ (k1_wellord2 @ X41) @ X40) = (k1_wellord2 @ X40))
% 1.53/1.77          | ~ (r1_tarski @ X40 @ X41))),
% 1.53/1.77      inference('cnf', [status(esa)], [t8_wellord2])).
% 1.53/1.77  thf('42', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X0)
% 1.53/1.77          | (zip_tseitin_1 @ X1 @ X2 @ X0)
% 1.53/1.77          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ 
% 1.53/1.77              (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 1.53/1.77              = (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))))),
% 1.53/1.77      inference('sup-', [status(thm)], ['40', '41'])).
% 1.53/1.77  thf(t57_wellord1, axiom,
% 1.53/1.77    (![A:$i]:
% 1.53/1.77     ( ( v1_relat_1 @ A ) =>
% 1.53/1.77       ( ( v2_wellord1 @ A ) =>
% 1.53/1.77         ( ![B:$i]:
% 1.53/1.77           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 1.53/1.77                ( r4_wellord1 @
% 1.53/1.77                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 1.53/1.77  thf('43', plain,
% 1.53/1.77      (![X30 : $i, X31 : $i]:
% 1.53/1.77         (~ (v2_wellord1 @ X30)
% 1.53/1.77          | ~ (r4_wellord1 @ X30 @ 
% 1.53/1.77               (k2_wellord1 @ X30 @ (k1_wellord1 @ X30 @ X31)))
% 1.53/1.77          | ~ (r2_hidden @ X31 @ (k3_relat_1 @ X30))
% 1.53/1.77          | ~ (v1_relat_1 @ X30))),
% 1.53/1.77      inference('cnf', [status(esa)], [t57_wellord1])).
% 1.53/1.77  thf('44', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 1.53/1.77             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 1.53/1.77          | (zip_tseitin_1 @ X0 @ X2 @ X1)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 1.53/1.77          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 1.53/1.77          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['42', '43'])).
% 1.53/1.77  thf('45', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('46', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 1.53/1.77      inference('demod', [status(thm)], ['16', '17'])).
% 1.53/1.77  thf('47', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 1.53/1.77             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 1.53/1.77          | (zip_tseitin_1 @ X0 @ X2 @ X1)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | ~ (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 1.53/1.77      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.53/1.77  thf('48', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.53/1.77         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | (zip_tseitin_1 @ X0 @ X3 @ X1)
% 1.53/1.77          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 1.53/1.77          | ~ (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | (zip_tseitin_1 @ X0 @ X2 @ X1))),
% 1.53/1.77      inference('sup-', [status(thm)], ['12', '47'])).
% 1.53/1.77  thf('49', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X0 @ X2 @ X1)
% 1.53/1.77          | ~ (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 1.53/1.77          | (zip_tseitin_1 @ X0 @ X3 @ X1)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 1.53/1.77      inference('simplify', [status(thm)], ['48'])).
% 1.53/1.77  thf('50', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ sk_A)
% 1.53/1.77          | ~ (v3_ordinal1 @ sk_B)
% 1.53/1.77          | (zip_tseitin_1 @ sk_B @ X0 @ sk_A)
% 1.53/1.77          | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77          | ~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77          | (zip_tseitin_1 @ sk_B @ X1 @ sk_A))),
% 1.53/1.77      inference('sup-', [status(thm)], ['9', '49'])).
% 1.53/1.77  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('52', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('53', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ sk_B @ X0 @ sk_A)
% 1.53/1.77          | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77          | ~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77          | (zip_tseitin_1 @ sk_B @ X1 @ sk_A))),
% 1.53/1.77      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.53/1.77  thf('54', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ sk_A)
% 1.53/1.77          | (zip_tseitin_1 @ sk_B @ X0 @ sk_A)
% 1.53/1.77          | ~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77          | (zip_tseitin_1 @ sk_B @ X1 @ sk_A))),
% 1.53/1.77      inference('sup-', [status(thm)], ['8', '53'])).
% 1.53/1.77  thf('55', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('56', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ sk_B @ X0 @ sk_A)
% 1.53/1.77          | ~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77          | (zip_tseitin_1 @ sk_B @ X1 @ sk_A))),
% 1.53/1.77      inference('demod', [status(thm)], ['54', '55'])).
% 1.53/1.77  thf('57', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ sk_B @ X0 @ sk_A) | ~ (r2_hidden @ sk_B @ sk_A))),
% 1.53/1.77      inference('condensation', [status(thm)], ['56'])).
% 1.53/1.77  thf('58', plain,
% 1.53/1.77      (![X19 : $i, X22 : $i, X23 : $i]:
% 1.53/1.77         ((zip_tseitin_1 @ X19 @ X22 @ X23) | (r2_hidden @ X19 @ X23))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.53/1.77  thf('59', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_B @ X0 @ sk_A)),
% 1.53/1.77      inference('clc', [status(thm)], ['57', '58'])).
% 1.53/1.77  thf('60', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.53/1.77          | ~ (zip_tseitin_1 @ X1 @ X0 @ X3)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3)
% 1.53/1.77          | ~ (r2_hidden @ X1 @ X3))),
% 1.53/1.77      inference('sup-', [status(thm)], ['31', '32'])).
% 1.53/1.77  thf('61', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X1 @ (k1_wellord1 @ X0 @ sk_B)) @ sk_A)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ X0 @ sk_B) @ X1)
% 1.53/1.77          | ~ (v1_relat_1 @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['59', '60'])).
% 1.53/1.77  thf('62', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ sk_B)
% 1.53/1.77          | (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77          | ((sk_B) = (sk_A))
% 1.53/1.77          | ~ (v3_ordinal1 @ sk_A)
% 1.53/1.77          | ~ (v1_relat_1 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ X0 @ sk_B) @ X1)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X1 @ (k1_wellord1 @ X0 @ sk_B)) @ sk_A))),
% 1.53/1.77      inference('sup-', [status(thm)], ['7', '61'])).
% 1.53/1.77  thf('63', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('64', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('65', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         ((r2_hidden @ sk_A @ sk_B)
% 1.53/1.77          | ((sk_B) = (sk_A))
% 1.53/1.77          | ~ (v1_relat_1 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ X0 @ sk_B) @ X1)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X1 @ (k1_wellord1 @ X0 @ sk_B)) @ sk_A))),
% 1.53/1.77      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.53/1.77  thf('66', plain, (((sk_A) != (sk_B))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('67', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         ((r2_hidden @ sk_A @ sk_B)
% 1.53/1.77          | ~ (v1_relat_1 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ X0 @ sk_B) @ X1)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X1 @ (k1_wellord1 @ X0 @ sk_B)) @ sk_A))),
% 1.53/1.77      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 1.53/1.77  thf('68', plain,
% 1.53/1.77      (![X1 : $i, X3 : $i]:
% 1.53/1.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.53/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.53/1.77  thf('69', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         ((r1_tarski @ (k1_wellord1 @ X0 @ sk_B) @ sk_A)
% 1.53/1.77          | ~ (v1_relat_1 @ X0)
% 1.53/1.77          | (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ X0 @ sk_B) @ sk_A))),
% 1.53/1.77      inference('sup-', [status(thm)], ['67', '68'])).
% 1.53/1.77  thf('70', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         ((r2_hidden @ sk_A @ sk_B)
% 1.53/1.77          | ~ (v1_relat_1 @ X0)
% 1.53/1.77          | (r1_tarski @ (k1_wellord1 @ X0 @ sk_B) @ sk_A))),
% 1.53/1.77      inference('simplify', [status(thm)], ['69'])).
% 1.53/1.77  thf('71', plain,
% 1.53/1.77      (![X40 : $i, X41 : $i]:
% 1.53/1.77         (((k2_wellord1 @ (k1_wellord2 @ X41) @ X40) = (k1_wellord2 @ X40))
% 1.53/1.77          | ~ (r1_tarski @ X40 @ X41))),
% 1.53/1.77      inference('cnf', [status(esa)], [t8_wellord2])).
% 1.53/1.77  thf('72', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X0)
% 1.53/1.77          | (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77          | ((k2_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord1 @ X0 @ sk_B))
% 1.53/1.77              = (k1_wellord2 @ (k1_wellord1 @ X0 @ sk_B))))),
% 1.53/1.77      inference('sup-', [status(thm)], ['70', '71'])).
% 1.53/1.77  thf('73', plain,
% 1.53/1.77      (![X30 : $i, X31 : $i]:
% 1.53/1.77         (~ (v2_wellord1 @ X30)
% 1.53/1.77          | ~ (r4_wellord1 @ X30 @ 
% 1.53/1.77               (k2_wellord1 @ X30 @ (k1_wellord1 @ X30 @ X31)))
% 1.53/1.77          | ~ (r2_hidden @ X31 @ (k3_relat_1 @ X30))
% 1.53/1.77          | ~ (v1_relat_1 @ X30))),
% 1.53/1.77      inference('cnf', [status(esa)], [t57_wellord1])).
% 1.53/1.77  thf('74', plain,
% 1.53/1.77      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ 
% 1.53/1.77           (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B)))
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ (k1_wellord2 @ sk_A)))
% 1.53/1.77        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['72', '73'])).
% 1.53/1.77  thf('75', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('76', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('77', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 1.53/1.77      inference('demod', [status(thm)], ['16', '17'])).
% 1.53/1.77  thf('78', plain,
% 1.53/1.77      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ 
% 1.53/1.77           (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B)))
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77        | ~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 1.53/1.77      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 1.53/1.77  thf('79', plain,
% 1.53/1.77      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))
% 1.53/1.77        | ~ (v3_ordinal1 @ sk_B)
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77        | ((sk_B) = (sk_A))
% 1.53/1.77        | ~ (v3_ordinal1 @ sk_A)
% 1.53/1.77        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77        | ~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B))),
% 1.53/1.77      inference('sup-', [status(thm)], ['6', '78'])).
% 1.53/1.77  thf('80', plain,
% 1.53/1.77      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('81', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('82', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('83', plain,
% 1.53/1.77      (((r2_hidden @ sk_A @ sk_B)
% 1.53/1.77        | ((sk_B) = (sk_A))
% 1.53/1.77        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77        | ~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B))),
% 1.53/1.77      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 1.53/1.77  thf('84', plain,
% 1.53/1.77      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77        | ((sk_B) = (sk_A))
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B))),
% 1.53/1.77      inference('simplify', [status(thm)], ['83'])).
% 1.53/1.77  thf('85', plain, (((sk_A) != (sk_B))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('86', plain,
% 1.53/1.77      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B))),
% 1.53/1.77      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 1.53/1.77  thf('87', plain,
% 1.53/1.77      ((~ (v3_ordinal1 @ sk_A)
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77        | ~ (r2_hidden @ sk_B @ sk_A))),
% 1.53/1.77      inference('sup-', [status(thm)], ['2', '86'])).
% 1.53/1.77  thf('88', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('89', plain, (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 1.53/1.77      inference('demod', [status(thm)], ['87', '88'])).
% 1.53/1.77  thf('90', plain,
% 1.53/1.77      ((~ (v3_ordinal1 @ sk_B)
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77        | ((sk_B) = (sk_A))
% 1.53/1.77        | ~ (v3_ordinal1 @ sk_A)
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B))),
% 1.53/1.77      inference('sup-', [status(thm)], ['1', '89'])).
% 1.53/1.77  thf('91', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('92', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('93', plain,
% 1.53/1.77      (((r2_hidden @ sk_A @ sk_B)
% 1.53/1.77        | ((sk_B) = (sk_A))
% 1.53/1.77        | (r2_hidden @ sk_A @ sk_B))),
% 1.53/1.77      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.53/1.77  thf('94', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 1.53/1.77      inference('simplify', [status(thm)], ['93'])).
% 1.53/1.77  thf('95', plain, (((sk_A) != (sk_B))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('96', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.53/1.77      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.53/1.77  thf('97', plain,
% 1.53/1.77      (![X37 : $i, X38 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X37)
% 1.53/1.77          | ((X38) = (k1_wellord1 @ (k1_wellord2 @ X37) @ X38))
% 1.53/1.77          | ~ (r2_hidden @ X38 @ X37)
% 1.53/1.77          | ~ (v3_ordinal1 @ X38))),
% 1.53/1.77      inference('cnf', [status(esa)], [t10_wellord2])).
% 1.53/1.77  thf('98', plain,
% 1.53/1.77      ((~ (v3_ordinal1 @ sk_A)
% 1.53/1.77        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 1.53/1.77        | ~ (v3_ordinal1 @ sk_B))),
% 1.53/1.77      inference('sup-', [status(thm)], ['96', '97'])).
% 1.53/1.77  thf('99', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('100', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('101', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 1.53/1.77      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.53/1.77  thf('102', plain,
% 1.53/1.77      (![X30 : $i, X31 : $i]:
% 1.53/1.77         (~ (v2_wellord1 @ X30)
% 1.53/1.77          | ~ (r4_wellord1 @ X30 @ 
% 1.53/1.77               (k2_wellord1 @ X30 @ (k1_wellord1 @ X30 @ X31)))
% 1.53/1.77          | ~ (r2_hidden @ X31 @ (k3_relat_1 @ X30))
% 1.53/1.77          | ~ (v1_relat_1 @ X30))),
% 1.53/1.77      inference('cnf', [status(esa)], [t57_wellord1])).
% 1.53/1.77  thf('103', plain,
% 1.53/1.77      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 1.53/1.77           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 1.53/1.77        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 1.53/1.77        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 1.53/1.77        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['101', '102'])).
% 1.53/1.77  thf('104', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('105', plain,
% 1.53/1.77      (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 1.53/1.77      inference('demod', [status(thm)], ['16', '17'])).
% 1.53/1.77  thf('106', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.53/1.77      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.53/1.77  thf('107', plain,
% 1.53/1.77      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ 
% 1.53/1.77           (k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 1.53/1.77        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B)))),
% 1.53/1.77      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 1.53/1.77  thf('108', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X0) | (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['14', '26'])).
% 1.53/1.77  thf('109', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.53/1.77      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.53/1.77  thf('110', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X0) | (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['14', '26'])).
% 1.53/1.77  thf('111', plain,
% 1.53/1.77      (![X1 : $i, X3 : $i]:
% 1.53/1.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.53/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.53/1.77  thf('112', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i]:
% 1.53/1.77         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | ((X1) = (X0))
% 1.53/1.77          | (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1))),
% 1.53/1.77      inference('simplify', [status(thm)], ['5'])).
% 1.53/1.77  thf('113', plain,
% 1.53/1.77      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X11)
% 1.53/1.77          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X11 @ X10))
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11))),
% 1.53/1.77      inference('simplify', [status(thm)], ['29'])).
% 1.53/1.77  thf('114', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (r2_hidden @ X2 @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | (r2_hidden @ X1 @ X0)
% 1.53/1.77          | ((X0) = (X1))
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ (k1_wellord2 @ X1))
% 1.53/1.77          | ~ (v1_relat_1 @ (k1_wellord2 @ X1)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['112', '113'])).
% 1.53/1.77  thf('115', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('116', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (r2_hidden @ X2 @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | (r2_hidden @ X1 @ X0)
% 1.53/1.77          | ((X0) = (X1))
% 1.53/1.77          | ~ (v3_ordinal1 @ X1)
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ (k1_wellord2 @ X1)))),
% 1.53/1.77      inference('demod', [status(thm)], ['114', '115'])).
% 1.53/1.77  thf('117', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         ((r1_tarski @ X0 @ X1)
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ X0) @ 
% 1.53/1.77             (k1_wellord2 @ X2))
% 1.53/1.77          | ~ (v3_ordinal1 @ X2)
% 1.53/1.77          | ((X0) = (X2))
% 1.53/1.77          | (r2_hidden @ X2 @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['111', '116'])).
% 1.53/1.77  thf('118', plain,
% 1.53/1.77      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.77         (~ (r2_hidden @ X19 @ X20)
% 1.53/1.77          | ~ (r2_hidden @ (k4_tarski @ X21 @ X19) @ X22)
% 1.53/1.77          | (r2_hidden @ X21 @ X20)
% 1.53/1.77          | ~ (zip_tseitin_1 @ X19 @ X22 @ X20))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.53/1.77  thf('119', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X1)
% 1.53/1.77          | (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ((X1) = (X0))
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | (r1_tarski @ X1 @ X2)
% 1.53/1.77          | ~ (zip_tseitin_1 @ X1 @ (k1_wellord2 @ X0) @ X3)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X2 @ X1) @ X3)
% 1.53/1.77          | ~ (r2_hidden @ X1 @ X3))),
% 1.53/1.77      inference('sup-', [status(thm)], ['117', '118'])).
% 1.53/1.77  thf('120', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X0)
% 1.53/1.77          | ~ (r2_hidden @ X1 @ X0)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X2 @ X1) @ X0)
% 1.53/1.77          | (r1_tarski @ X1 @ X2)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0)
% 1.53/1.77          | ((X1) = (X0))
% 1.53/1.77          | (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ~ (v3_ordinal1 @ X1))),
% 1.53/1.77      inference('sup-', [status(thm)], ['110', '119'])).
% 1.53/1.77  thf('121', plain,
% 1.53/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X1)
% 1.53/1.77          | (r2_hidden @ X0 @ X1)
% 1.53/1.77          | ((X1) = (X0))
% 1.53/1.77          | (r1_tarski @ X1 @ X2)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X2 @ X1) @ X0)
% 1.53/1.77          | ~ (r2_hidden @ X1 @ X0)
% 1.53/1.77          | ~ (v3_ordinal1 @ X0))),
% 1.53/1.77      inference('simplify', [status(thm)], ['120'])).
% 1.53/1.77  thf('122', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ sk_B)
% 1.53/1.77          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 1.53/1.77          | (r1_tarski @ sk_A @ X0)
% 1.53/1.77          | ((sk_A) = (sk_B))
% 1.53/1.77          | (r2_hidden @ sk_B @ sk_A)
% 1.53/1.77          | ~ (v3_ordinal1 @ sk_A))),
% 1.53/1.77      inference('sup-', [status(thm)], ['109', '121'])).
% 1.53/1.77  thf('123', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('124', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('125', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 1.53/1.77          | (r1_tarski @ sk_A @ X0)
% 1.53/1.77          | ((sk_A) = (sk_B))
% 1.53/1.77          | (r2_hidden @ sk_B @ sk_A))),
% 1.53/1.77      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.53/1.77  thf('126', plain, (((sk_A) != (sk_B))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('127', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 1.53/1.77          | (r1_tarski @ sk_A @ X0)
% 1.53/1.77          | (r2_hidden @ sk_B @ sk_A))),
% 1.53/1.77      inference('simplify_reflect-', [status(thm)], ['125', '126'])).
% 1.53/1.77  thf('128', plain,
% 1.53/1.77      (![X1 : $i, X3 : $i]:
% 1.53/1.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.53/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.53/1.77  thf('129', plain,
% 1.53/1.77      (((r2_hidden @ sk_B @ sk_A)
% 1.53/1.77        | (r1_tarski @ sk_A @ sk_B)
% 1.53/1.77        | (r1_tarski @ sk_A @ sk_B))),
% 1.53/1.77      inference('sup-', [status(thm)], ['127', '128'])).
% 1.53/1.77  thf('130', plain, (((r1_tarski @ sk_A @ sk_B) | (r2_hidden @ sk_B @ sk_A))),
% 1.53/1.77      inference('simplify', [status(thm)], ['129'])).
% 1.53/1.77  thf('131', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 1.53/1.77      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.53/1.77  thf('132', plain,
% 1.53/1.77      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X11)
% 1.53/1.77          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ X11 @ X10))
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ X13 @ X10) @ X11))),
% 1.53/1.77      inference('simplify', [status(thm)], ['29'])).
% 1.53/1.77  thf('133', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         (~ (r2_hidden @ X0 @ sk_A)
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ (k1_wellord2 @ sk_B))
% 1.53/1.77          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['131', '132'])).
% 1.53/1.77  thf('134', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('135', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         (~ (r2_hidden @ X0 @ sk_A)
% 1.53/1.77          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ (k1_wellord2 @ sk_B)))),
% 1.53/1.77      inference('demod', [status(thm)], ['133', '134'])).
% 1.53/1.77  thf('136', plain,
% 1.53/1.77      (((r1_tarski @ sk_A @ sk_B)
% 1.53/1.77        | (r2_hidden @ (k4_tarski @ sk_B @ sk_A) @ (k1_wellord2 @ sk_B)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['130', '135'])).
% 1.53/1.77  thf('137', plain,
% 1.53/1.77      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.77         (~ (r2_hidden @ X19 @ X20)
% 1.53/1.77          | ~ (r2_hidden @ (k4_tarski @ X21 @ X19) @ X22)
% 1.53/1.77          | (r2_hidden @ X21 @ X20)
% 1.53/1.77          | ~ (zip_tseitin_1 @ X19 @ X22 @ X20))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.53/1.77  thf('138', plain,
% 1.53/1.77      (![X0 : $i]:
% 1.53/1.77         ((r1_tarski @ sk_A @ sk_B)
% 1.53/1.77          | ~ (zip_tseitin_1 @ sk_A @ (k1_wellord2 @ sk_B) @ X0)
% 1.53/1.77          | (r2_hidden @ sk_B @ X0)
% 1.53/1.77          | ~ (r2_hidden @ sk_A @ X0))),
% 1.53/1.77      inference('sup-', [status(thm)], ['136', '137'])).
% 1.53/1.77  thf('139', plain,
% 1.53/1.77      ((~ (v3_ordinal1 @ sk_B)
% 1.53/1.77        | ~ (r2_hidden @ sk_A @ sk_B)
% 1.53/1.77        | (r2_hidden @ sk_B @ sk_B)
% 1.53/1.77        | (r1_tarski @ sk_A @ sk_B))),
% 1.53/1.77      inference('sup-', [status(thm)], ['108', '138'])).
% 1.53/1.77  thf('140', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('141', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.53/1.77      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.53/1.77  thf('142', plain, (((r2_hidden @ sk_B @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 1.53/1.77      inference('demod', [status(thm)], ['139', '140', '141'])).
% 1.53/1.77  thf('143', plain, (((r1_tarski @ sk_A @ sk_B) | (r2_hidden @ sk_B @ sk_A))),
% 1.53/1.77      inference('simplify', [status(thm)], ['129'])).
% 1.53/1.77  thf('144', plain,
% 1.53/1.77      (![X37 : $i, X38 : $i]:
% 1.53/1.77         (~ (v3_ordinal1 @ X37)
% 1.53/1.77          | ((X38) = (k1_wellord1 @ (k1_wellord2 @ X37) @ X38))
% 1.53/1.77          | ~ (r2_hidden @ X38 @ X37)
% 1.53/1.77          | ~ (v3_ordinal1 @ X38))),
% 1.53/1.77      inference('cnf', [status(esa)], [t10_wellord2])).
% 1.53/1.77  thf('145', plain,
% 1.53/1.77      (((r1_tarski @ sk_A @ sk_B)
% 1.53/1.77        | ~ (v3_ordinal1 @ sk_B)
% 1.53/1.77        | ((sk_B) = (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B))
% 1.53/1.77        | ~ (v3_ordinal1 @ sk_A))),
% 1.53/1.77      inference('sup-', [status(thm)], ['143', '144'])).
% 1.53/1.77  thf('146', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('147', plain, ((v3_ordinal1 @ sk_A)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('148', plain,
% 1.53/1.77      (((r1_tarski @ sk_A @ sk_B)
% 1.53/1.77        | ((sk_B) = (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B)))),
% 1.53/1.77      inference('demod', [status(thm)], ['145', '146', '147'])).
% 1.53/1.77  thf('149', plain,
% 1.53/1.77      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.53/1.77         (((X12) != (k1_wellord1 @ X11 @ X10))
% 1.53/1.77          | ((X13) != (X10))
% 1.53/1.77          | ~ (r2_hidden @ X13 @ X12)
% 1.53/1.77          | ~ (v1_relat_1 @ X11))),
% 1.53/1.77      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.53/1.77  thf('150', plain,
% 1.53/1.77      (![X10 : $i, X11 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X11)
% 1.53/1.77          | ~ (r2_hidden @ X10 @ (k1_wellord1 @ X11 @ X10)))),
% 1.53/1.77      inference('simplify', [status(thm)], ['149'])).
% 1.53/1.77  thf('151', plain,
% 1.53/1.77      ((~ (r2_hidden @ sk_B @ sk_B)
% 1.53/1.77        | (r1_tarski @ sk_A @ sk_B)
% 1.53/1.77        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['148', '150'])).
% 1.53/1.77  thf('152', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('153', plain,
% 1.53/1.77      ((~ (r2_hidden @ sk_B @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 1.53/1.77      inference('demod', [status(thm)], ['151', '152'])).
% 1.53/1.77  thf('154', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.53/1.77      inference('clc', [status(thm)], ['142', '153'])).
% 1.53/1.77  thf('155', plain,
% 1.53/1.77      (![X40 : $i, X41 : $i]:
% 1.53/1.77         (((k2_wellord1 @ (k1_wellord2 @ X41) @ X40) = (k1_wellord2 @ X40))
% 1.53/1.77          | ~ (r1_tarski @ X40 @ X41))),
% 1.53/1.77      inference('cnf', [status(esa)], [t8_wellord2])).
% 1.53/1.77  thf('156', plain,
% 1.53/1.77      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 1.53/1.77      inference('sup-', [status(thm)], ['154', '155'])).
% 1.53/1.77  thf('157', plain,
% 1.53/1.77      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf(t50_wellord1, axiom,
% 1.53/1.77    (![A:$i]:
% 1.53/1.77     ( ( v1_relat_1 @ A ) =>
% 1.53/1.77       ( ![B:$i]:
% 1.53/1.77         ( ( v1_relat_1 @ B ) =>
% 1.53/1.77           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 1.53/1.77  thf('158', plain,
% 1.53/1.77      (![X28 : $i, X29 : $i]:
% 1.53/1.77         (~ (v1_relat_1 @ X28)
% 1.53/1.77          | (r4_wellord1 @ X28 @ X29)
% 1.53/1.77          | ~ (r4_wellord1 @ X29 @ X28)
% 1.53/1.77          | ~ (v1_relat_1 @ X29))),
% 1.53/1.77      inference('cnf', [status(esa)], [t50_wellord1])).
% 1.53/1.77  thf('159', plain,
% 1.53/1.77      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 1.53/1.77        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 1.53/1.77        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 1.53/1.77      inference('sup-', [status(thm)], ['157', '158'])).
% 1.53/1.77  thf('160', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('161', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 1.53/1.77      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 1.53/1.77  thf('162', plain,
% 1.53/1.77      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 1.53/1.77      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.53/1.77  thf('163', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 1.53/1.77      inference('demod', [status(thm)], ['107', '156', '162'])).
% 1.53/1.77  thf('164', plain, (~ (v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('sup-', [status(thm)], ['0', '163'])).
% 1.53/1.77  thf('165', plain, ((v3_ordinal1 @ sk_B)),
% 1.53/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.77  thf('166', plain, ($false), inference('demod', [status(thm)], ['164', '165'])).
% 1.53/1.77  
% 1.53/1.77  % SZS output end Refutation
% 1.53/1.77  
% 1.53/1.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
