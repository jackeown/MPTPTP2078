%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0649+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.79nCvqh3dN

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:15 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 138 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  744 (1966 expanded)
%              Number of equality atoms :   52 ( 133 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t56_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_2 @ X14 @ X16 @ X17 )
      | ( X16
       != ( k1_funct_1 @ X17 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X14: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X17 ) )
      | ( zip_tseitin_2 @ X14 @ ( k1_funct_1 @ X17 @ X14 ) @ X17 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    zip_tseitin_2 @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','2'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
        & ( D
          = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_9,axiom,(
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

thf('6',plain,(
    ! [X23: $i,X24: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
       != ( k2_funct_1 @ X23 ) )
      | ( zip_tseitin_3 @ X27 @ X26 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('7',plain,(
    ! [X23: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( zip_tseitin_3 @ X27 @ X26 @ ( k2_funct_1 @ X23 ) @ X23 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_2 @ X18 @ X19 @ X20 )
      | ( X18
        = ( k1_funct_1 @ X21 @ X19 ) )
      | ~ ( zip_tseitin_3 @ X18 @ X19 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X3 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X2 @ X3 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( sk_A
       != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( sk_A
       != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A
       != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf('39',plain,
    ( $false
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('41',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('42',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['27'])).

thf('45',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['39','45'])).


%------------------------------------------------------------------------------
