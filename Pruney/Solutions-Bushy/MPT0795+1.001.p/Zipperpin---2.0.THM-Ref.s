%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0795+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hwDN7RsuKQ

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 310 expanded)
%              Number of leaves         :   25 ( 110 expanded)
%              Depth                    :   23
%              Number of atoms          : 1790 (6380 expanded)
%              Number of equality atoms :   30 ( 184 expanded)
%              Maximal formula depth    :   20 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
        & ( r2_hidden @ E @ ( k3_relat_1 @ A ) )
        & ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B ) ) ) )).

thf(zf_stmt_2,axiom,(
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

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ X8 )
       != ( k3_relat_1 @ X7 ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k3_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ( zip_tseitin_0 @ ( sk_E @ X8 @ X6 @ X7 ) @ ( sk_D @ X8 @ X6 @ X7 ) @ X8 @ X6 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ ( sk_E @ X8 @ X6 @ X7 ) ) @ X7 )
      | ( r3_wellord1 @ X7 @ X6 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r3_wellord1 @ X1 @ X2 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ X0 ) @ X2 @ X1 ) @ ( sk_E @ ( k6_relat_1 @ X0 ) @ X2 @ X1 ) ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ X0 ) @ X2 @ X1 ) @ ( sk_D @ ( k6_relat_1 @ X0 ) @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) @ X2 @ X1 )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
       != ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ! [X13: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('6',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r3_wellord1 @ X1 @ X2 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ X0 ) @ X2 @ X1 ) @ ( sk_E @ ( k6_relat_1 @ X0 ) @ X2 @ X1 ) ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ X0 ) @ X2 @ X1 ) @ ( sk_D @ ( k6_relat_1 @ X0 ) @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) @ X2 @ X1 )
      | ( X0
       != ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k3_relat_1 @ X1 )
       != ( k3_relat_1 @ X2 ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X1 ) ) @ X2 @ X1 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X1 ) ) @ X2 @ X1 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X1 ) ) @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X1 ) ) @ X2 @ X1 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X1 ) ) @ X2 @ X1 ) ) @ X1 )
      | ( r3_wellord1 @ X1 @ X2 @ ( k6_relat_1 @ ( k3_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_relat_1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ ( k3_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ ( k3_relat_1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X16 @ ( k3_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X20 ) @ X19 )
        = X19 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) )
        = ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X20 ) @ X19 )
        = X19 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) )
        = ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X3 @ X0 ) @ ( k1_funct_1 @ X3 @ X2 ) ) @ X4 )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) )
        = ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) )
        = ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('37',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ X3 @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X3 @ X0 ) @ ( k1_funct_1 @ X3 @ X2 ) ) @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k3_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X2 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_relat_1 @ X3 ) )
      | ( zip_tseitin_0 @ X2 @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X1 @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X2 ) )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X2 ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X1 @ X2 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X1 ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X1 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ X8 )
       != ( k3_relat_1 @ X7 ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k3_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( zip_tseitin_0 @ ( sk_E @ X8 @ X6 @ X7 ) @ ( sk_D @ X8 @ X6 @ X7 ) @ X8 @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ ( sk_E @ X8 @ X6 @ X7 ) ) @ X7 )
      | ( r3_wellord1 @ X7 @ X6 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
       != ( k3_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
       != ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    ! [X13: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('53',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('54',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ( ( k3_relat_1 @ X0 )
       != ( k3_relat_1 @ X0 ) )
      | ( ( k3_relat_1 @ X0 )
       != ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['46','56'])).

thf(t47_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r3_wellord1 @ A @ A @ ( k6_relat_1 @ ( k3_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( r3_wellord1 @ A @ A @ ( k6_relat_1 @ ( k3_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_wellord1])).

thf('58',plain,(
    ~ ( r3_wellord1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60'])).


%------------------------------------------------------------------------------
