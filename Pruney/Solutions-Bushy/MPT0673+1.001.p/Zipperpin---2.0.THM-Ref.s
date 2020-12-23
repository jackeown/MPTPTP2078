%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0673+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e1ILDR8wMu

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:18 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 164 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   33
%              Number of atoms          : 1680 (2307 expanded)
%              Number of equality atoms :   48 (  66 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

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

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16
       != ( k8_relat_1 @ X17 @ X15 ) )
      | ( zip_tseitin_1 @ X20 @ X15 @ X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('6',plain,(
    ! [X15: $i,X17: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X17 @ X15 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k8_relat_1 @ X17 @ X15 ) ) )
      | ( zip_tseitin_1 @ X20 @ X15 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( zip_tseitin_1 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_B @ ( k8_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16
       != ( k8_relat_1 @ X17 @ X15 ) )
      | ( zip_tseitin_0 @ X18 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('20',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X17 @ X15 ) )
      | ( zip_tseitin_0 @ X18 @ X15 @ ( k8_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_funct_1 @ X8 @ X7 )
        = ( k1_funct_1 @ X9 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_funct_1 @ X8 @ X7 )
        = ( k1_funct_1 @ X9 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X0 ) @ X1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_funct_1 @ X1 @ ( sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('58',plain,(
    ! [X15: $i,X17: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X17 @ X15 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k8_relat_1 @ X17 @ X15 ) ) )
      | ( zip_tseitin_1 @ X20 @ X15 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( zip_tseitin_1 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_C @ ( k8_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) )
        = X2 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) )
        = X2 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
       != ( k1_funct_1 @ X0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( sk_B @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf(t99_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( v2_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( v2_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t99_funct_1])).

thf('75',plain,(
    ~ ( v2_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( ( sk_C @ ( k8_relat_1 @ sk_A @ sk_B_1 ) )
      = ( sk_B @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( sk_C @ ( k8_relat_1 @ sk_A @ sk_B_1 ) )
    = ( sk_B @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('82',plain,
    ( ( ( sk_B @ ( k8_relat_1 @ sk_A @ sk_B_1 ) )
     != ( sk_B @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) )
    | ( v2_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( v2_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,(
    ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['89','90','91'])).


%------------------------------------------------------------------------------
