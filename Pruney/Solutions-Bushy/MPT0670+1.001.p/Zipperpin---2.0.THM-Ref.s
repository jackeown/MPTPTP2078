%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0670+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CdkwC95MJB

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  321 ( 435 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(t85_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_relat_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_relat_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) )
              & ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
        & ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
       => ( ( k1_funct_1 @ B @ D )
          = ( k1_funct_1 @ C @ D ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( zip_tseitin_1 @ D @ C @ A ) )
              & ! [D: $i] :
                  ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13
       != ( k8_relat_1 @ X14 @ X12 ) )
      | ( zip_tseitin_0 @ X15 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('3',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X14 @ X12 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X14 @ X12 ) )
      | ( zip_tseitin_0 @ X15 @ X12 @ ( k8_relat_1 @ X14 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t87_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
       => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
         => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_1])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) )
      | ( ( k1_funct_1 @ X5 @ X4 )
        = ( k1_funct_1 @ X6 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ sk_A @ X0 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).


%------------------------------------------------------------------------------
