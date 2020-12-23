%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zgnqrtk7gh

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   56 (  65 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  532 ( 616 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t54_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ! [C: $i,D: $i] :
                    ( ( ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) )
                     => ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) )
                    & ( ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) )
                     => ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) )
                & ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
        & ( D
          = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) )
                & ! [C: $i,D: $i] :
                    ( ( zip_tseitin_3 @ D @ C @ B @ A )
                    & ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
       != ( k2_funct_1 @ X22 ) )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('5',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X27 ) @ X27 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t62_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf(zf_stmt_9,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_1])).

thf('20',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('23',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('24',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zgnqrtk7gh
% 0.12/0.36  % Computer   : n016.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 12:49:19 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.23/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.47  % Solved by: fo/fo7.sh
% 0.23/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.47  % done 32 iterations in 0.022s
% 0.23/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.47  % SZS output start Refutation
% 0.23/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.23/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.47  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.23/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.23/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.23/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.47  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.23/0.47  thf(dt_k2_funct_1, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.47       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.47         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.23/0.47  thf('0', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.47  thf('1', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.47  thf('2', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.47  thf('3', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.47  thf(t54_funct_1, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.23/0.47       ( ( v2_funct_1 @ A ) =>
% 0.23/0.47         ( ![B:$i]:
% 0.23/0.47           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.23/0.47             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.23/0.47               ( ( ![C:$i,D:$i]:
% 0.23/0.47                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.23/0.47                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.23/0.47                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.23/0.47                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.23/0.47                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.23/0.47                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.23/0.47                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.23/0.47                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.23/0.47                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_0, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.23/0.47  thf(zf_stmt_1, axiom,
% 0.23/0.47    (![D:$i,C:$i,B:$i,A:$i]:
% 0.23/0.47     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.23/0.47       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.23/0.47         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.23/0.47           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.23/0.47  thf(zf_stmt_3, axiom,
% 0.23/0.47    (![D:$i,C:$i,A:$i]:
% 0.23/0.47     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.23/0.47       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.23/0.47         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.23/0.47  thf(zf_stmt_5, axiom,
% 0.23/0.47    (![D:$i,C:$i,B:$i,A:$i]:
% 0.23/0.47     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.23/0.47       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.23/0.47         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.23/0.47           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.23/0.47  thf(zf_stmt_7, axiom,
% 0.23/0.47    (![D:$i,C:$i,B:$i,A:$i]:
% 0.23/0.47     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.23/0.47       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.23/0.47         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_8, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.47       ( ( v2_funct_1 @ A ) =>
% 0.23/0.47         ( ![B:$i]:
% 0.23/0.47           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.47             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.23/0.47               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.23/0.47                 ( ![C:$i,D:$i]:
% 0.23/0.47                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.23/0.47                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.23/0.47  thf('4', plain,
% 0.23/0.47      (![X22 : $i, X23 : $i]:
% 0.23/0.47         (~ (v2_funct_1 @ X22)
% 0.23/0.47          | ~ (v1_relat_1 @ X23)
% 0.23/0.47          | ~ (v1_funct_1 @ X23)
% 0.23/0.47          | ((X23) != (k2_funct_1 @ X22))
% 0.23/0.47          | ((k1_relat_1 @ X23) = (k2_relat_1 @ X22))
% 0.23/0.47          | ~ (v1_funct_1 @ X22)
% 0.23/0.47          | ~ (v1_relat_1 @ X22))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.23/0.47  thf('5', plain,
% 0.23/0.47      (![X22 : $i]:
% 0.23/0.47         (~ (v1_relat_1 @ X22)
% 0.23/0.47          | ~ (v1_funct_1 @ X22)
% 0.23/0.47          | ((k1_relat_1 @ (k2_funct_1 @ X22)) = (k2_relat_1 @ X22))
% 0.23/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X22))
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X22))
% 0.23/0.47          | ~ (v2_funct_1 @ X22))),
% 0.23/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.23/0.47  thf('6', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('sup-', [status(thm)], ['3', '5'])).
% 0.23/0.47  thf('7', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.23/0.47  thf('8', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['2', '7'])).
% 0.23/0.47  thf('9', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.23/0.47  thf(t61_funct_1, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.47       ( ( v2_funct_1 @ A ) =>
% 0.23/0.47         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.23/0.47             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.23/0.47           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.23/0.47             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.23/0.47  thf('10', plain,
% 0.23/0.47      (![X27 : $i]:
% 0.23/0.47         (~ (v2_funct_1 @ X27)
% 0.23/0.47          | ((k5_relat_1 @ (k2_funct_1 @ X27) @ X27)
% 0.23/0.47              = (k6_relat_1 @ (k2_relat_1 @ X27)))
% 0.23/0.47          | ~ (v1_funct_1 @ X27)
% 0.23/0.47          | ~ (v1_relat_1 @ X27))),
% 0.23/0.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.23/0.47  thf(t53_funct_1, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.47       ( ( ?[B:$i]:
% 0.23/0.47           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.23/0.47             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.23/0.47         ( v2_funct_1 @ A ) ) ))).
% 0.23/0.47  thf('11', plain,
% 0.23/0.47      (![X1 : $i, X2 : $i]:
% 0.23/0.47         (~ (v1_relat_1 @ X1)
% 0.23/0.47          | ~ (v1_funct_1 @ X1)
% 0.23/0.47          | ((k5_relat_1 @ X2 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X2)))
% 0.23/0.47          | (v2_funct_1 @ X2)
% 0.23/0.47          | ~ (v1_funct_1 @ X2)
% 0.23/0.47          | ~ (v1_relat_1 @ X2))),
% 0.23/0.47      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.23/0.47  thf('12', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.23/0.47            != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.23/0.47          | ~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.47  thf('13', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0)
% 0.23/0.47          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.23/0.47              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.23/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.47  thf('14', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.23/0.47          | ~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['9', '13'])).
% 0.23/0.47  thf('15', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.23/0.47  thf('16', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['1', '15'])).
% 0.23/0.47  thf('17', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.23/0.47  thf('18', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['0', '17'])).
% 0.23/0.47  thf('19', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.47          | ~ (v2_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_funct_1 @ X0)
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.23/0.47  thf(t62_funct_1, conjecture,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.47       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_9, negated_conjecture,
% 0.23/0.47    (~( ![A:$i]:
% 0.23/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.47          ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )),
% 0.23/0.47    inference('cnf.neg', [status(esa)], [t62_funct_1])).
% 0.23/0.47  thf('20', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.23/0.47  thf('21', plain,
% 0.23/0.47      ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A) | ~ (v2_funct_1 @ sk_A))),
% 0.23/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.47  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.23/0.47  thf('23', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.23/0.47  thf('24', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.23/0.47  thf('25', plain, ($false),
% 0.23/0.47      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.23/0.47  
% 0.23/0.47  % SZS output end Refutation
% 0.23/0.47  
% 0.23/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
