%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UbuMErQOtD

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 310 expanded)
%              Number of leaves         :   25 ( 110 expanded)
%              Depth                    :   23
%              Number of atoms          : 1787 (6347 expanded)
%              Number of equality atoms :   30 ( 184 expanded)
%              Maximal formula depth    :   20 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ X18 )
       != ( k3_relat_1 @ X17 ) )
      | ( ( k2_relat_1 @ X18 )
       != ( k3_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( zip_tseitin_0 @ ( sk_E @ X18 @ X16 @ X17 ) @ ( sk_D @ X18 @ X16 @ X17 ) @ X18 @ X16 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ ( sk_E @ X18 @ X16 @ X17 ) ) @ X17 )
      | ( r3_wellord1 @ X17 @ X16 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k3_relat_1 @ X11 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 @ X11 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X10 @ ( k3_relat_1 @ X11 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r3_wellord1 @ X0 @ X0 @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( sk_E @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ ( k6_relat_1 @ ( k3_relat_1 @ X0 ) ) @ X0 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X13 @ X10 ) @ ( k1_funct_1 @ X13 @ X12 ) ) @ X14 )
      | ~ ( zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 @ X11 ) ) ),
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
    ! [X10: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ X13 @ X10 ) @ ( k1_funct_1 @ X13 @ X12 ) ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ X15 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ X18 )
       != ( k3_relat_1 @ X17 ) )
      | ( ( k2_relat_1 @ X18 )
       != ( k3_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( zip_tseitin_0 @ ( sk_E @ X18 @ X16 @ X17 ) @ ( sk_D @ X18 @ X16 @ X17 ) @ X18 @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ ( sk_E @ X18 @ X16 @ X17 ) ) @ X17 )
      | ( r3_wellord1 @ X17 @ X16 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('53',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('54',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UbuMErQOtD
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 71 iterations in 0.080s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.19/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.50  thf(t71_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.50  thf('0', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf(d7_wellord1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( v1_relat_1 @ B ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.19/0.50               ( ( r3_wellord1 @ A @ B @ C ) <=>
% 0.19/0.50                 ( ( ![D:$i,E:$i]:
% 0.19/0.50                     ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) <=>
% 0.19/0.50                       ( ( r2_hidden @
% 0.19/0.50                           ( k4_tarski @
% 0.19/0.50                             ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ 
% 0.19/0.50                           B ) & 
% 0.19/0.50                         ( r2_hidden @ E @ ( k3_relat_1 @ A ) ) & 
% 0.19/0.50                         ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) ) ) ) & 
% 0.19/0.50                   ( v2_funct_1 @ C ) & 
% 0.19/0.50                   ( ( k2_relat_1 @ C ) = ( k3_relat_1 @ B ) ) & 
% 0.19/0.50                   ( ( k1_relat_1 @ C ) = ( k3_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.19/0.50  thf(zf_stmt_1, axiom,
% 0.19/0.50    (![E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.19/0.50     ( ( zip_tseitin_0 @ E @ D @ C @ B @ A ) <=>
% 0.19/0.50       ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.19/0.50         ( r2_hidden @ E @ ( k3_relat_1 @ A ) ) & 
% 0.19/0.50         ( r2_hidden @
% 0.19/0.50           ( k4_tarski @ ( k1_funct_1 @ C @ D ) @ ( k1_funct_1 @ C @ E ) ) @ B ) ) ))).
% 0.19/0.50  thf(zf_stmt_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( v1_relat_1 @ B ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.50               ( ( r3_wellord1 @ A @ B @ C ) <=>
% 0.19/0.50                 ( ( ( k1_relat_1 @ C ) = ( k3_relat_1 @ A ) ) & 
% 0.19/0.50                   ( ( k2_relat_1 @ C ) = ( k3_relat_1 @ B ) ) & 
% 0.19/0.50                   ( v2_funct_1 @ C ) & 
% 0.19/0.50                   ( ![D:$i,E:$i]:
% 0.19/0.50                     ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) <=>
% 0.19/0.50                       ( zip_tseitin_0 @ E @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X16)
% 0.19/0.50          | ((k1_relat_1 @ X18) != (k3_relat_1 @ X17))
% 0.19/0.50          | ((k2_relat_1 @ X18) != (k3_relat_1 @ X16))
% 0.19/0.50          | ~ (v2_funct_1 @ X18)
% 0.19/0.50          | (zip_tseitin_0 @ (sk_E @ X18 @ X16 @ X17) @ 
% 0.19/0.50             (sk_D @ X18 @ X16 @ X17) @ X18 @ X16 @ X17)
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ (sk_E @ X18 @ X16 @ X17)) @ 
% 0.19/0.50             X17)
% 0.19/0.50          | (r3_wellord1 @ X17 @ X16 @ X18)
% 0.19/0.50          | ~ (v1_funct_1 @ X18)
% 0.19/0.50          | ~ (v1_relat_1 @ X18)
% 0.19/0.50          | ~ (v1_relat_1 @ X17))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (((X0) != (k3_relat_1 @ X1))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.19/0.50          | (r3_wellord1 @ X1 @ X2 @ (k6_relat_1 @ X0))
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (k4_tarski @ (sk_D @ (k6_relat_1 @ X0) @ X2 @ X1) @ 
% 0.19/0.50              (sk_E @ (k6_relat_1 @ X0) @ X2 @ X1)) @ 
% 0.19/0.50             X1)
% 0.19/0.50          | (zip_tseitin_0 @ (sk_E @ (k6_relat_1 @ X0) @ X2 @ X1) @ 
% 0.19/0.50             (sk_D @ (k6_relat_1 @ X0) @ X2 @ X1) @ (k6_relat_1 @ X0) @ X2 @ X1)
% 0.19/0.50          | ~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.19/0.50          | ((k2_relat_1 @ (k6_relat_1 @ X0)) != (k3_relat_1 @ X2))
% 0.19/0.50          | ~ (v1_relat_1 @ X2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf(fc3_funct_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.50  thf('3', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.50  thf('4', plain, (![X6 : $i]: (v1_funct_1 @ (k6_relat_1 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.50  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.19/0.50  thf('5', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.19/0.50  thf('6', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (((X0) != (k3_relat_1 @ X1))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | (r3_wellord1 @ X1 @ X2 @ (k6_relat_1 @ X0))
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (k4_tarski @ (sk_D @ (k6_relat_1 @ X0) @ X2 @ X1) @ 
% 0.19/0.50              (sk_E @ (k6_relat_1 @ X0) @ X2 @ X1)) @ 
% 0.19/0.50             X1)
% 0.19/0.50          | (zip_tseitin_0 @ (sk_E @ (k6_relat_1 @ X0) @ X2 @ X1) @ 
% 0.19/0.50             (sk_D @ (k6_relat_1 @ X0) @ X2 @ X1) @ (k6_relat_1 @ X0) @ X2 @ X1)
% 0.19/0.50          | ((X0) != (k3_relat_1 @ X2))
% 0.19/0.50          | ~ (v1_relat_1 @ X2))),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X2)
% 0.19/0.50          | ((k3_relat_1 @ X1) != (k3_relat_1 @ X2))
% 0.19/0.50          | (zip_tseitin_0 @ 
% 0.19/0.50             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X1)) @ X2 @ X1) @ 
% 0.19/0.50             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X1)) @ X2 @ X1) @ 
% 0.19/0.50             (k6_relat_1 @ (k3_relat_1 @ X1)) @ X2 @ X1)
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (k4_tarski @ 
% 0.19/0.50              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X1)) @ X2 @ X1) @ 
% 0.19/0.50              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X1)) @ X2 @ X1)) @ 
% 0.19/0.50             X1)
% 0.19/0.50          | (r3_wellord1 @ X1 @ X2 @ (k6_relat_1 @ (k3_relat_1 @ X1)))
% 0.19/0.50          | ~ (v1_relat_1 @ X1))),
% 0.19/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X0)
% 0.19/0.50          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.50          | (r2_hidden @ 
% 0.19/0.50             (k4_tarski @ 
% 0.19/0.50              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.50              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.50             X0)
% 0.19/0.50          | (zip_tseitin_0 @ 
% 0.19/0.50             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.50             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.50             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.50          | ~ (v1_relat_1 @ X0))),
% 0.19/0.50      inference('eq_res', [status(thm)], ['8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.51         ((zip_tseitin_0 @ 
% 0.19/0.51           (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.51         ((r2_hidden @ X12 @ (k3_relat_1 @ X11))
% 0.19/0.51          | ~ (zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0)
% 0.19/0.51          | (r2_hidden @ (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.51  thf(t30_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ C ) =>
% 0.19/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.19/0.51         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.19/0.51           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.19/0.51          | (r2_hidden @ X1 @ (k3_relat_1 @ X2))
% 0.19/0.51          | ~ (v1_relat_1 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (k3_relat_1 @ X0))
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r2_hidden @ (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((zip_tseitin_0 @ 
% 0.19/0.51           (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.51         ((r2_hidden @ X10 @ (k3_relat_1 @ X11))
% 0.19/0.51          | ~ (zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0)
% 0.19/0.51          | (r2_hidden @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.19/0.51          | (r2_hidden @ X0 @ (k3_relat_1 @ X2))
% 0.19/0.51          | ~ (v1_relat_1 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (k3_relat_1 @ X0))
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r2_hidden @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.51  thf(t35_funct_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.19/0.51       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]:
% 0.19/0.51         (((k1_funct_1 @ (k6_relat_1 @ X8) @ X7) = (X7))
% 0.19/0.51          | ~ (r2_hidden @ X7 @ X8))),
% 0.19/0.51      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0))
% 0.19/0.51              = (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]:
% 0.19/0.51         (((k1_funct_1 @ (k6_relat_1 @ X8) @ X7) = (X7))
% 0.19/0.51          | ~ (r2_hidden @ X7 @ X8))),
% 0.19/0.51      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0))
% 0.19/0.51              = (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((zip_tseitin_0 @ 
% 0.19/0.51           (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.51         ((r2_hidden @ 
% 0.19/0.51           (k4_tarski @ (k1_funct_1 @ X13 @ X10) @ (k1_funct_1 @ X13 @ X12)) @ 
% 0.19/0.51           X14)
% 0.19/0.51          | ~ (zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0)
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ 
% 0.19/0.51               (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51              (k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0))) @ 
% 0.19/0.51             X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ 
% 0.19/0.51           (k4_tarski @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51            (k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0))) @ 
% 0.19/0.51           X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['27', '30'])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ 
% 0.19/0.51           (k4_tarski @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51            (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51           X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0))) @ 
% 0.19/0.51             X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ 
% 0.19/0.51           (k4_tarski @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51            (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51           X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['24', '32'])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0))
% 0.19/0.51              = (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0))
% 0.19/0.51              = (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.51         ((zip_tseitin_0 @ X12 @ X10 @ X13 @ X14 @ X15)
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (k4_tarski @ (k1_funct_1 @ X13 @ X10) @ (k1_funct_1 @ X13 @ X12)) @ 
% 0.19/0.51               X14)
% 0.19/0.51          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X15))
% 0.19/0.51          | ~ (r2_hidden @ X10 @ (k3_relat_1 @ X15)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.51         (~ (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (k1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X2)) @ 
% 0.19/0.51             X1)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k3_relat_1 @ X3))
% 0.19/0.51          | ~ (r2_hidden @ X2 @ (k3_relat_1 @ X3))
% 0.19/0.51          | (zip_tseitin_0 @ X2 @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X1 @ X3))),
% 0.19/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X1)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (zip_tseitin_0 @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X1 @ X2)
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k3_relat_1 @ X2))
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k3_relat_1 @ X2))
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['35', '38'])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r2_hidden @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X2))
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k3_relat_1 @ X2))
% 0.19/0.51          | (zip_tseitin_0 @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X1 @ X2)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (k4_tarski @ 
% 0.19/0.51                (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51                (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51               X1))),
% 0.19/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (zip_tseitin_0 @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X1)
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k3_relat_1 @ X1))
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k3_relat_1 @ X1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['34', '40'])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r2_hidden @ (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X1))
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k3_relat_1 @ X1))
% 0.19/0.51          | (zip_tseitin_0 @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X1)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (zip_tseitin_0 @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k3_relat_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '42'])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (r2_hidden @ (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k3_relat_1 @ X0))
% 0.19/0.51          | (zip_tseitin_0 @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0))))),
% 0.19/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (zip_tseitin_0 @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '44'])).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((zip_tseitin_0 @ 
% 0.19/0.51           (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51           (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0))))),
% 0.19/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r2_hidden @ 
% 0.19/0.51             (k4_tarski @ 
% 0.19/0.51              (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51              (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)) @ 
% 0.19/0.51             X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X16)
% 0.19/0.51          | ((k1_relat_1 @ X18) != (k3_relat_1 @ X17))
% 0.19/0.51          | ((k2_relat_1 @ X18) != (k3_relat_1 @ X16))
% 0.19/0.51          | ~ (v2_funct_1 @ X18)
% 0.19/0.51          | ~ (zip_tseitin_0 @ (sk_E @ X18 @ X16 @ X17) @ 
% 0.19/0.51               (sk_D @ X18 @ X16 @ X17) @ X18 @ X16 @ X17)
% 0.19/0.51          | ~ (r2_hidden @ 
% 0.19/0.51               (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ (sk_E @ X18 @ X16 @ X17)) @ 
% 0.19/0.51               X17)
% 0.19/0.51          | (r3_wellord1 @ X17 @ X16 @ X18)
% 0.19/0.51          | ~ (v1_funct_1 @ X18)
% 0.19/0.51          | ~ (v1_relat_1 @ X18)
% 0.19/0.51          | ~ (v1_relat_1 @ X17))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (zip_tseitin_0 @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | ~ (v2_funct_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ((k2_relat_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51              != (k3_relat_1 @ X0))
% 0.19/0.51          | ((k1_relat_1 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51              != (k3_relat_1 @ X0))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.51  thf('50', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.51  thf('51', plain, (![X6 : $i]: (v1_funct_1 @ (k6_relat_1 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.51  thf('52', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 0.19/0.51      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.19/0.51  thf('53', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.51  thf('54', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (zip_tseitin_0 @ 
% 0.19/0.51               (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51               (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | ((k3_relat_1 @ X0) != (k3_relat_1 @ X0))
% 0.19/0.51          | ((k3_relat_1 @ X0) != (k3_relat_1 @ X0))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (zip_tseitin_0 @ 
% 0.19/0.51             (sk_E @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (sk_D @ (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0) @ 
% 0.19/0.51             (k6_relat_1 @ (k3_relat_1 @ X0)) @ X0 @ X0)
% 0.19/0.51          | (r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['55'])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r3_wellord1 @ X0 @ X0 @ (k6_relat_1 @ (k3_relat_1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('clc', [status(thm)], ['46', '56'])).
% 0.19/0.51  thf(t47_wellord1, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( r3_wellord1 @ A @ A @ ( k6_relat_1 @ ( k3_relat_1 @ A ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_3, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( v1_relat_1 @ A ) =>
% 0.19/0.51          ( r3_wellord1 @ A @ A @ ( k6_relat_1 @ ( k3_relat_1 @ A ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t47_wellord1])).
% 0.19/0.51  thf('58', plain,
% 0.19/0.51      (~ (r3_wellord1 @ sk_A @ sk_A @ (k6_relat_1 @ (k3_relat_1 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.51  thf('59', plain, (~ (v1_relat_1 @ sk_A)),
% 0.19/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.51  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.51  thf('61', plain, ($false), inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
