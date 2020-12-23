%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TPFzCwCSxY

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 147 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  637 (2022 expanded)
%              Number of equality atoms :   35 ( 117 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

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

thf('10',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X13 @ X14 )
      | ( X13
       != ( k1_funct_1 @ X14 @ X11 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X14 ) )
      | ( zip_tseitin_2 @ X11 @ ( k1_funct_1 @ X14 @ X11 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    zip_tseitin_2 @ sk_C_1 @ ( k1_funct_1 @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','12'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X20: $i,X21: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X21
       != ( k2_funct_1 @ X20 ) )
      | ( zip_tseitin_3 @ X24 @ X23 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('17',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( zip_tseitin_3 @ X24 @ X23 @ ( k2_funct_1 @ X20 ) @ X20 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_2 @ X15 @ X16 @ X17 )
      | ( X15
        = ( k1_funct_1 @ X18 @ X16 ) )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_C_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26','29'])).

thf('31',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('33',plain,(
    zip_tseitin_2 @ sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C_1 )
    = ( k1_funct_1 @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    zip_tseitin_2 @ sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('37',plain,
    ( ( sk_D_1
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('41',plain,
    ( sk_D_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    sk_D_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['30','41'])).

thf('43',plain,(
    sk_C_1 != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TPFzCwCSxY
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 60 iterations in 0.032s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.46  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.21/0.46  thf(t85_funct_2, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.46       ( ( v2_funct_1 @ B ) =>
% 0.21/0.46         ( ![C:$i,D:$i]:
% 0.21/0.46           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.46               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.46             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.46            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.46          ( ( v2_funct_1 @ B ) =>
% 0.21/0.46            ( ![C:$i,D:$i]:
% 0.21/0.46              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.46                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.46                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.21/0.46  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t67_funct_2, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.46       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X31 : $i, X32 : $i]:
% 0.21/0.46         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.21/0.46          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.21/0.46          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.21/0.46          | ~ (v1_funct_1 @ X32))),
% 0.21/0.46      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.46        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.46         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.21/0.46          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.46  thf('8', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.21/0.46  thf(t54_funct_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.46       ( ( v2_funct_1 @ A ) =>
% 0.21/0.46         ( ![B:$i]:
% 0.21/0.46           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.46             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.46               ( ( ![C:$i,D:$i]:
% 0.21/0.46                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.46                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.21/0.46                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.46                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.21/0.46                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.46                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.21/0.46                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.21/0.46                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.21/0.46                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_1, axiom,
% 0.21/0.46    (![D:$i,C:$i,A:$i]:
% 0.21/0.46     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.21/0.46       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.46         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.46         ((zip_tseitin_2 @ X11 @ X13 @ X14)
% 0.21/0.46          | ((X13) != (k1_funct_1 @ X14 @ X11))
% 0.21/0.46          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X14)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X11 : $i, X14 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X14))
% 0.21/0.46          | (zip_tseitin_2 @ X11 @ (k1_funct_1 @ X14 @ X11) @ X14))),
% 0.21/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.46          | (zip_tseitin_2 @ X0 @ (k1_funct_1 @ sk_B @ X0) @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((zip_tseitin_2 @ sk_C_1 @ (k1_funct_1 @ sk_B @ sk_C_1) @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '12'])).
% 0.21/0.46  thf(dt_k2_funct_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.46       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.46         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.46  thf(zf_stmt_2, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.21/0.46  thf(zf_stmt_3, axiom,
% 0.21/0.46    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.46     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.21/0.46       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.21/0.46         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.46           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.46  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.46  thf(zf_stmt_6, axiom,
% 0.21/0.46    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.46     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.21/0.46       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.21/0.46         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.46           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.46  thf(zf_stmt_8, axiom,
% 0.21/0.46    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.46     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.46       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.46         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_9, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.46       ( ( v2_funct_1 @ A ) =>
% 0.21/0.46         ( ![B:$i]:
% 0.21/0.46           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.46             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.21/0.46               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.21/0.46                 ( ![C:$i,D:$i]:
% 0.21/0.46                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.21/0.46                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X20 : $i, X21 : $i, X23 : $i, X24 : $i]:
% 0.21/0.46         (~ (v2_funct_1 @ X20)
% 0.21/0.46          | ~ (v1_relat_1 @ X21)
% 0.21/0.46          | ~ (v1_funct_1 @ X21)
% 0.21/0.46          | ((X21) != (k2_funct_1 @ X20))
% 0.21/0.46          | (zip_tseitin_3 @ X24 @ X23 @ X21 @ X20)
% 0.21/0.46          | ~ (v1_funct_1 @ X20)
% 0.21/0.46          | ~ (v1_relat_1 @ X20))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X20 : $i, X23 : $i, X24 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X20)
% 0.21/0.46          | ~ (v1_funct_1 @ X20)
% 0.21/0.46          | (zip_tseitin_3 @ X24 @ X23 @ (k2_funct_1 @ X20) @ X20)
% 0.21/0.46          | ~ (v1_funct_1 @ (k2_funct_1 @ X20))
% 0.21/0.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X20))
% 0.21/0.46          | ~ (v2_funct_1 @ X20))),
% 0.21/0.46      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v2_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.46          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.46          | ~ (v2_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v2_funct_1 @ X0)
% 0.21/0.46          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.46          | ~ (v2_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.46         (~ (zip_tseitin_2 @ X15 @ X16 @ X17)
% 0.21/0.46          | ((X15) = (k1_funct_1 @ X18 @ X16))
% 0.21/0.46          | ~ (zip_tseitin_3 @ X15 @ X16 @ X18 @ X17))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v2_funct_1 @ X0)
% 0.21/0.46          | ((X2) = (k1_funct_1 @ (k2_funct_1 @ X0) @ X1))
% 0.21/0.46          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      ((((sk_C_1)
% 0.21/0.46          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C_1)))
% 0.21/0.46        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.46        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['13', '23'])).
% 0.21/0.46  thf('25', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(cc1_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( v1_relat_1 @ C ) ))).
% 0.21/0.46  thf('28', plain,
% 0.21/0.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.46         ((v1_relat_1 @ X25)
% 0.21/0.46          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.46  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      (((sk_C_1)
% 0.21/0.46         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C_1)))),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25', '26', '29'])).
% 0.21/0.46  thf('31', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('32', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.46          | (zip_tseitin_2 @ X0 @ (k1_funct_1 @ sk_B @ X0) @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.46  thf('33', plain,
% 0.21/0.46      ((zip_tseitin_2 @ sk_D_1 @ (k1_funct_1 @ sk_B @ sk_D_1) @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.46  thf('34', plain,
% 0.21/0.46      (((k1_funct_1 @ sk_B @ sk_C_1) = (k1_funct_1 @ sk_B @ sk_D_1))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('35', plain,
% 0.21/0.46      ((zip_tseitin_2 @ sk_D_1 @ (k1_funct_1 @ sk_B @ sk_C_1) @ sk_B)),
% 0.21/0.46      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.46  thf('36', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v2_funct_1 @ X0)
% 0.21/0.46          | ((X2) = (k1_funct_1 @ (k2_funct_1 @ X0) @ X1))
% 0.21/0.46          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.46  thf('37', plain,
% 0.21/0.46      ((((sk_D_1)
% 0.21/0.46          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C_1)))
% 0.21/0.46        | ~ (v2_funct_1 @ sk_B)
% 0.21/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.46        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.46  thf('38', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.46  thf('41', plain,
% 0.21/0.46      (((sk_D_1)
% 0.21/0.46         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C_1)))),
% 0.21/0.46      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.21/0.46  thf('42', plain, (((sk_D_1) = (sk_C_1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['30', '41'])).
% 0.21/0.46  thf('43', plain, (((sk_C_1) != (sk_D_1))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('44', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
