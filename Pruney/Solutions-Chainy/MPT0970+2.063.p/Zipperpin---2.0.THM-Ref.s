%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6vLmTHgXI7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:25 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 442 expanded)
%              Number of leaves         :   40 ( 142 expanded)
%              Depth                    :   21
%              Number of atoms          :  946 (6969 expanded)
%              Number of equality atoms :   65 ( 476 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ ( sk_D_4 @ X33 @ X31 ) @ X31 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
        = X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B )
    | ( r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X44 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_B )
      | ( X44
        = ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17 = k1_xboole_0 )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X18 ) @ X16 )
      | ( X18
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) @ sk_C_3 )
    | ( ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['10','16'])).

thf('18',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) @ sk_C_3 )
    | ( ( sk_D_4 @ sk_C_3 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','19','24'])).

thf('26',plain,(
    ! [X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X35 @ ( sk_D_4 @ X33 @ X31 ) ) @ X33 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
        = X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_4 @ sk_C_3 @ sk_B )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B )
    | ( ( sk_D_4 @ sk_C_3 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_E_1 @ k1_xboole_0 ) @ sk_A ),
    inference(demod,[status(thm)],['6','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('33',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,
    ( ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('47',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('49',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('51',plain,(
    ~ ( r1_tarski @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['41','53'])).

thf('55',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['38','54'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X20: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( X24
       != ( k1_funct_1 @ X20 @ X25 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('57',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['22','23'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ k1_xboole_0 ) ) @ ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['31','61'])).

thf('63',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('64',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('65',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('66',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    r2_hidden @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['62','66'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('68',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X10 @ X8 ) @ X10 ) @ X8 )
      | ( X9
       != ( k2_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('69',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X10 @ X8 ) @ X10 ) @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ sk_C_3 ) @ k1_xboole_0 ) @ sk_C_3 ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('73',plain,(
    ! [X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X35 @ ( sk_D_4 @ X33 @ X31 ) ) @ X33 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
        = X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ k1_xboole_0 ) @ sk_C_3 )
      | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
        = sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ k1_xboole_0 ) @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ X0 @ k1_xboole_0 ) @ sk_C_3 ) ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('sup-',[status(thm)],['70','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6vLmTHgXI7
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 12:07:45 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 2.24/2.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.24/2.40  % Solved by: fo/fo7.sh
% 2.24/2.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.24/2.40  % done 1315 iterations in 1.922s
% 2.24/2.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.24/2.40  % SZS output start Refutation
% 2.24/2.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.24/2.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.24/2.40  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 2.24/2.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.24/2.40  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.24/2.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.24/2.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.24/2.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.24/2.40  thf(sk_A_type, type, sk_A: $i).
% 2.24/2.40  thf(sk_C_3_type, type, sk_C_3: $i).
% 2.24/2.40  thf(sk_B_type, type, sk_B: $i).
% 2.24/2.40  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.24/2.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.24/2.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.24/2.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.24/2.40  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.24/2.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.24/2.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.24/2.40  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.24/2.40  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 2.24/2.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.24/2.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.24/2.40  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.24/2.40  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.24/2.40  thf(t16_funct_2, conjecture,
% 2.24/2.40    (![A:$i,B:$i,C:$i]:
% 2.24/2.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.24/2.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.24/2.40       ( ( ![D:$i]:
% 2.24/2.40           ( ~( ( r2_hidden @ D @ B ) & 
% 2.24/2.40                ( ![E:$i]:
% 2.24/2.40                  ( ~( ( r2_hidden @ E @ A ) & 
% 2.24/2.40                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 2.24/2.40         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 2.24/2.40  thf(zf_stmt_0, negated_conjecture,
% 2.24/2.40    (~( ![A:$i,B:$i,C:$i]:
% 2.24/2.40        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.24/2.40            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.24/2.40          ( ( ![D:$i]:
% 2.24/2.40              ( ~( ( r2_hidden @ D @ B ) & 
% 2.24/2.40                   ( ![E:$i]:
% 2.24/2.40                     ( ~( ( r2_hidden @ E @ A ) & 
% 2.24/2.40                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 2.24/2.40            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 2.24/2.40    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 2.24/2.40  thf('0', plain,
% 2.24/2.40      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf(t23_relset_1, axiom,
% 2.24/2.40    (![A:$i,B:$i,C:$i]:
% 2.24/2.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.24/2.40       ( ( ![D:$i]:
% 2.24/2.40           ( ~( ( r2_hidden @ D @ B ) & 
% 2.24/2.40                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 2.24/2.40         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 2.24/2.40  thf('1', plain,
% 2.24/2.40      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.24/2.40         ((r2_hidden @ (sk_D_4 @ X33 @ X31) @ X31)
% 2.24/2.40          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 2.24/2.40          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.24/2.40      inference('cnf', [status(esa)], [t23_relset_1])).
% 2.24/2.40  thf('2', plain,
% 2.24/2.40      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))
% 2.24/2.40        | (r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B))),
% 2.24/2.40      inference('sup-', [status(thm)], ['0', '1'])).
% 2.24/2.40  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) != (sk_B))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('4', plain, ((r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B)),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 2.24/2.40  thf('5', plain,
% 2.24/2.40      (![X44 : $i]:
% 2.24/2.40         (~ (r2_hidden @ X44 @ sk_B) | (r2_hidden @ (sk_E_1 @ X44) @ sk_A))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('6', plain, ((r2_hidden @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B)) @ sk_A)),
% 2.24/2.40      inference('sup-', [status(thm)], ['4', '5'])).
% 2.24/2.40  thf('7', plain,
% 2.24/2.40      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('8', plain, ((r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B)),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 2.24/2.40  thf('9', plain,
% 2.24/2.40      (![X44 : $i]:
% 2.24/2.40         (~ (r2_hidden @ X44 @ sk_B)
% 2.24/2.40          | ((X44) = (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ X44))))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('10', plain,
% 2.24/2.40      (((sk_D_4 @ sk_C_3 @ sk_B)
% 2.24/2.40         = (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B))))),
% 2.24/2.40      inference('sup-', [status(thm)], ['8', '9'])).
% 2.24/2.40  thf(d4_funct_1, axiom,
% 2.24/2.40    (![A:$i]:
% 2.24/2.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.24/2.40       ( ![B:$i,C:$i]:
% 2.24/2.40         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 2.24/2.40             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 2.24/2.40               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 2.24/2.40           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 2.24/2.40             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 2.24/2.40               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 2.24/2.40  thf('11', plain,
% 2.24/2.40      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.24/2.40         ((r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 2.24/2.40          | ((X17) = (k1_xboole_0))
% 2.24/2.40          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 2.24/2.40          | ~ (v1_funct_1 @ X16)
% 2.24/2.40          | ~ (v1_relat_1 @ X16))),
% 2.24/2.40      inference('cnf', [status(esa)], [d4_funct_1])).
% 2.24/2.40  thf('12', plain,
% 2.24/2.40      (![X15 : $i, X16 : $i]:
% 2.24/2.40         (~ (v1_relat_1 @ X16)
% 2.24/2.40          | ~ (v1_funct_1 @ X16)
% 2.24/2.40          | ((k1_funct_1 @ X16 @ X15) = (k1_xboole_0))
% 2.24/2.40          | (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 2.24/2.40      inference('simplify', [status(thm)], ['11'])).
% 2.24/2.40  thf('13', plain,
% 2.24/2.40      (![X15 : $i, X16 : $i, X18 : $i]:
% 2.24/2.40         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 2.24/2.40          | (r2_hidden @ (k4_tarski @ X15 @ X18) @ X16)
% 2.24/2.40          | ((X18) != (k1_funct_1 @ X16 @ X15))
% 2.24/2.40          | ~ (v1_funct_1 @ X16)
% 2.24/2.40          | ~ (v1_relat_1 @ X16))),
% 2.24/2.40      inference('cnf', [status(esa)], [d4_funct_1])).
% 2.24/2.40  thf('14', plain,
% 2.24/2.40      (![X15 : $i, X16 : $i]:
% 2.24/2.40         (~ (v1_relat_1 @ X16)
% 2.24/2.40          | ~ (v1_funct_1 @ X16)
% 2.24/2.40          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 2.24/2.40          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 2.24/2.40      inference('simplify', [status(thm)], ['13'])).
% 2.24/2.40  thf('15', plain,
% 2.24/2.40      (![X0 : $i, X1 : $i]:
% 2.24/2.40         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 2.24/2.40          | ~ (v1_funct_1 @ X0)
% 2.24/2.40          | ~ (v1_relat_1 @ X0)
% 2.24/2.40          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 2.24/2.40          | ~ (v1_funct_1 @ X0)
% 2.24/2.40          | ~ (v1_relat_1 @ X0))),
% 2.24/2.40      inference('sup-', [status(thm)], ['12', '14'])).
% 2.24/2.40  thf('16', plain,
% 2.24/2.40      (![X0 : $i, X1 : $i]:
% 2.24/2.40         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 2.24/2.40          | ~ (v1_relat_1 @ X0)
% 2.24/2.40          | ~ (v1_funct_1 @ X0)
% 2.24/2.40          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 2.24/2.40      inference('simplify', [status(thm)], ['15'])).
% 2.24/2.40  thf('17', plain,
% 2.24/2.40      (((r2_hidden @ 
% 2.24/2.40         (k4_tarski @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B)) @ 
% 2.24/2.40          (sk_D_4 @ sk_C_3 @ sk_B)) @ 
% 2.24/2.40         sk_C_3)
% 2.24/2.40        | ((k1_funct_1 @ sk_C_3 @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B)))
% 2.24/2.40            = (k1_xboole_0))
% 2.24/2.40        | ~ (v1_funct_1 @ sk_C_3)
% 2.24/2.40        | ~ (v1_relat_1 @ sk_C_3))),
% 2.24/2.40      inference('sup+', [status(thm)], ['10', '16'])).
% 2.24/2.40  thf('18', plain,
% 2.24/2.40      (((sk_D_4 @ sk_C_3 @ sk_B)
% 2.24/2.40         = (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B))))),
% 2.24/2.40      inference('sup-', [status(thm)], ['8', '9'])).
% 2.24/2.40  thf('19', plain, ((v1_funct_1 @ sk_C_3)),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('20', plain,
% 2.24/2.40      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf(cc2_relat_1, axiom,
% 2.24/2.40    (![A:$i]:
% 2.24/2.40     ( ( v1_relat_1 @ A ) =>
% 2.24/2.40       ( ![B:$i]:
% 2.24/2.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.24/2.40  thf('21', plain,
% 2.24/2.40      (![X4 : $i, X5 : $i]:
% 2.24/2.40         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 2.24/2.40          | (v1_relat_1 @ X4)
% 2.24/2.40          | ~ (v1_relat_1 @ X5))),
% 2.24/2.40      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.24/2.40  thf('22', plain,
% 2.24/2.40      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_3))),
% 2.24/2.40      inference('sup-', [status(thm)], ['20', '21'])).
% 2.24/2.40  thf(fc6_relat_1, axiom,
% 2.24/2.40    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.24/2.40  thf('23', plain,
% 2.24/2.40      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 2.24/2.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.24/2.40  thf('24', plain, ((v1_relat_1 @ sk_C_3)),
% 2.24/2.40      inference('demod', [status(thm)], ['22', '23'])).
% 2.24/2.40  thf('25', plain,
% 2.24/2.40      (((r2_hidden @ 
% 2.24/2.40         (k4_tarski @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B)) @ 
% 2.24/2.40          (sk_D_4 @ sk_C_3 @ sk_B)) @ 
% 2.24/2.40         sk_C_3)
% 2.24/2.40        | ((sk_D_4 @ sk_C_3 @ sk_B) = (k1_xboole_0)))),
% 2.24/2.40      inference('demod', [status(thm)], ['17', '18', '19', '24'])).
% 2.24/2.40  thf('26', plain,
% 2.24/2.40      (![X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 2.24/2.40         (~ (r2_hidden @ (k4_tarski @ X35 @ (sk_D_4 @ X33 @ X31)) @ X33)
% 2.24/2.40          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 2.24/2.40          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.24/2.40      inference('cnf', [status(esa)], [t23_relset_1])).
% 2.24/2.40  thf('27', plain,
% 2.24/2.40      (![X0 : $i]:
% 2.24/2.40         (((sk_D_4 @ sk_C_3 @ sk_B) = (k1_xboole_0))
% 2.24/2.40          | ~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.24/2.40          | ((k2_relset_1 @ X0 @ sk_B @ sk_C_3) = (sk_B)))),
% 2.24/2.40      inference('sup-', [status(thm)], ['25', '26'])).
% 2.24/2.40  thf('28', plain,
% 2.24/2.40      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))
% 2.24/2.40        | ((sk_D_4 @ sk_C_3 @ sk_B) = (k1_xboole_0)))),
% 2.24/2.40      inference('sup-', [status(thm)], ['7', '27'])).
% 2.24/2.40  thf('29', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) != (sk_B))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('30', plain, (((sk_D_4 @ sk_C_3 @ sk_B) = (k1_xboole_0))),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 2.24/2.40  thf('31', plain, ((r2_hidden @ (sk_E_1 @ k1_xboole_0) @ sk_A)),
% 2.24/2.40      inference('demod', [status(thm)], ['6', '30'])).
% 2.24/2.40  thf('32', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf(d1_funct_2, axiom,
% 2.24/2.40    (![A:$i,B:$i,C:$i]:
% 2.24/2.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.24/2.40       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.24/2.40           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.24/2.40             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.24/2.40         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.24/2.40           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.24/2.40             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.24/2.40  thf(zf_stmt_1, axiom,
% 2.24/2.40    (![C:$i,B:$i,A:$i]:
% 2.24/2.40     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.24/2.40       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.24/2.40  thf('33', plain,
% 2.24/2.40      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.24/2.40         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 2.24/2.40          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 2.24/2.40          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.24/2.40  thf('34', plain,
% 2.24/2.40      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)
% 2.24/2.40        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_3)))),
% 2.24/2.40      inference('sup-', [status(thm)], ['32', '33'])).
% 2.24/2.40  thf('35', plain,
% 2.24/2.40      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf(redefinition_k1_relset_1, axiom,
% 2.24/2.40    (![A:$i,B:$i,C:$i]:
% 2.24/2.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.24/2.40       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.24/2.40  thf('36', plain,
% 2.24/2.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.24/2.40         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 2.24/2.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 2.24/2.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.24/2.40  thf('37', plain,
% 2.24/2.40      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 2.24/2.40      inference('sup-', [status(thm)], ['35', '36'])).
% 2.24/2.40  thf('38', plain,
% 2.24/2.40      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)
% 2.24/2.40        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.24/2.40      inference('demod', [status(thm)], ['34', '37'])).
% 2.24/2.40  thf('39', plain,
% 2.24/2.40      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.24/2.40  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.24/2.40  thf(zf_stmt_4, axiom,
% 2.24/2.40    (![B:$i,A:$i]:
% 2.24/2.40     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.24/2.40       ( zip_tseitin_0 @ B @ A ) ))).
% 2.24/2.40  thf(zf_stmt_5, axiom,
% 2.24/2.40    (![A:$i,B:$i,C:$i]:
% 2.24/2.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.24/2.40       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.24/2.40         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.24/2.40           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.24/2.40             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.24/2.40  thf('40', plain,
% 2.24/2.40      (![X41 : $i, X42 : $i, X43 : $i]:
% 2.24/2.40         (~ (zip_tseitin_0 @ X41 @ X42)
% 2.24/2.40          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 2.24/2.40          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.24/2.40  thf('41', plain,
% 2.24/2.40      (((zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)
% 2.24/2.40        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.24/2.40      inference('sup-', [status(thm)], ['39', '40'])).
% 2.24/2.40  thf(d3_tarski, axiom,
% 2.24/2.40    (![A:$i,B:$i]:
% 2.24/2.40     ( ( r1_tarski @ A @ B ) <=>
% 2.24/2.40       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.24/2.40  thf('42', plain,
% 2.24/2.40      (![X1 : $i, X3 : $i]:
% 2.24/2.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.24/2.40      inference('cnf', [status(esa)], [d3_tarski])).
% 2.24/2.40  thf('43', plain,
% 2.24/2.40      (![X1 : $i, X3 : $i]:
% 2.24/2.40         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.24/2.40      inference('cnf', [status(esa)], [d3_tarski])).
% 2.24/2.40  thf('44', plain,
% 2.24/2.40      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 2.24/2.40      inference('sup-', [status(thm)], ['42', '43'])).
% 2.24/2.40  thf('45', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.24/2.40      inference('simplify', [status(thm)], ['44'])).
% 2.24/2.40  thf('46', plain,
% 2.24/2.40      (![X36 : $i, X37 : $i]:
% 2.24/2.40         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.24/2.40  thf('47', plain, ((r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B)),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 2.24/2.40  thf(t7_ordinal1, axiom,
% 2.24/2.40    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.24/2.40  thf('48', plain,
% 2.24/2.40      (![X26 : $i, X27 : $i]:
% 2.24/2.40         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 2.24/2.40      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.24/2.40  thf('49', plain, (~ (r1_tarski @ sk_B @ (sk_D_4 @ sk_C_3 @ sk_B))),
% 2.24/2.40      inference('sup-', [status(thm)], ['47', '48'])).
% 2.24/2.40  thf('50', plain, (((sk_D_4 @ sk_C_3 @ sk_B) = (k1_xboole_0))),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 2.24/2.40  thf('51', plain, (~ (r1_tarski @ sk_B @ k1_xboole_0)),
% 2.24/2.40      inference('demod', [status(thm)], ['49', '50'])).
% 2.24/2.40  thf('52', plain,
% 2.24/2.40      (![X0 : $i, X1 : $i]:
% 2.24/2.40         (~ (r1_tarski @ sk_B @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.24/2.40      inference('sup-', [status(thm)], ['46', '51'])).
% 2.24/2.40  thf('53', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 2.24/2.40      inference('sup-', [status(thm)], ['45', '52'])).
% 2.24/2.40  thf('54', plain, ((zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)),
% 2.24/2.40      inference('demod', [status(thm)], ['41', '53'])).
% 2.24/2.40  thf('55', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 2.24/2.40      inference('demod', [status(thm)], ['38', '54'])).
% 2.24/2.40  thf(d5_funct_1, axiom,
% 2.24/2.40    (![A:$i]:
% 2.24/2.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.24/2.40       ( ![B:$i]:
% 2.24/2.40         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.24/2.40           ( ![C:$i]:
% 2.24/2.40             ( ( r2_hidden @ C @ B ) <=>
% 2.24/2.40               ( ?[D:$i]:
% 2.24/2.40                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 2.24/2.40                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 2.24/2.40  thf('56', plain,
% 2.24/2.40      (![X20 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 2.24/2.40         (((X22) != (k2_relat_1 @ X20))
% 2.24/2.40          | (r2_hidden @ X24 @ X22)
% 2.24/2.40          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 2.24/2.40          | ((X24) != (k1_funct_1 @ X20 @ X25))
% 2.24/2.40          | ~ (v1_funct_1 @ X20)
% 2.24/2.40          | ~ (v1_relat_1 @ X20))),
% 2.24/2.40      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.24/2.40  thf('57', plain,
% 2.24/2.40      (![X20 : $i, X25 : $i]:
% 2.24/2.40         (~ (v1_relat_1 @ X20)
% 2.24/2.40          | ~ (v1_funct_1 @ X20)
% 2.24/2.40          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 2.24/2.40          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 2.24/2.40      inference('simplify', [status(thm)], ['56'])).
% 2.24/2.40  thf('58', plain,
% 2.24/2.40      (![X0 : $i]:
% 2.24/2.40         (~ (r2_hidden @ X0 @ sk_A)
% 2.24/2.40          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ (k2_relat_1 @ sk_C_3))
% 2.24/2.40          | ~ (v1_funct_1 @ sk_C_3)
% 2.24/2.40          | ~ (v1_relat_1 @ sk_C_3))),
% 2.24/2.40      inference('sup-', [status(thm)], ['55', '57'])).
% 2.24/2.40  thf('59', plain, ((v1_funct_1 @ sk_C_3)),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('60', plain, ((v1_relat_1 @ sk_C_3)),
% 2.24/2.40      inference('demod', [status(thm)], ['22', '23'])).
% 2.24/2.40  thf('61', plain,
% 2.24/2.40      (![X0 : $i]:
% 2.24/2.40         (~ (r2_hidden @ X0 @ sk_A)
% 2.24/2.40          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ (k2_relat_1 @ sk_C_3)))),
% 2.24/2.40      inference('demod', [status(thm)], ['58', '59', '60'])).
% 2.24/2.40  thf('62', plain,
% 2.24/2.40      ((r2_hidden @ (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ k1_xboole_0)) @ 
% 2.24/2.40        (k2_relat_1 @ sk_C_3))),
% 2.24/2.40      inference('sup-', [status(thm)], ['31', '61'])).
% 2.24/2.40  thf('63', plain,
% 2.24/2.40      (((sk_D_4 @ sk_C_3 @ sk_B)
% 2.24/2.40         = (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B))))),
% 2.24/2.40      inference('sup-', [status(thm)], ['8', '9'])).
% 2.24/2.40  thf('64', plain, (((sk_D_4 @ sk_C_3 @ sk_B) = (k1_xboole_0))),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 2.24/2.40  thf('65', plain, (((sk_D_4 @ sk_C_3 @ sk_B) = (k1_xboole_0))),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 2.24/2.40  thf('66', plain,
% 2.24/2.40      (((k1_xboole_0) = (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ k1_xboole_0)))),
% 2.24/2.40      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.24/2.40  thf('67', plain, ((r2_hidden @ k1_xboole_0 @ (k2_relat_1 @ sk_C_3))),
% 2.24/2.40      inference('demod', [status(thm)], ['62', '66'])).
% 2.24/2.40  thf(d5_relat_1, axiom,
% 2.24/2.40    (![A:$i,B:$i]:
% 2.24/2.40     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.24/2.40       ( ![C:$i]:
% 2.24/2.40         ( ( r2_hidden @ C @ B ) <=>
% 2.24/2.40           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 2.24/2.40  thf('68', plain,
% 2.24/2.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.24/2.40         (~ (r2_hidden @ X10 @ X9)
% 2.24/2.40          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X10 @ X8) @ X10) @ X8)
% 2.24/2.40          | ((X9) != (k2_relat_1 @ X8)))),
% 2.24/2.40      inference('cnf', [status(esa)], [d5_relat_1])).
% 2.24/2.40  thf('69', plain,
% 2.24/2.40      (![X8 : $i, X10 : $i]:
% 2.24/2.40         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X10 @ X8) @ X10) @ X8)
% 2.24/2.40          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X8)))),
% 2.24/2.40      inference('simplify', [status(thm)], ['68'])).
% 2.24/2.40  thf('70', plain,
% 2.24/2.40      ((r2_hidden @ 
% 2.24/2.40        (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ sk_C_3) @ k1_xboole_0) @ sk_C_3)),
% 2.24/2.40      inference('sup-', [status(thm)], ['67', '69'])).
% 2.24/2.40  thf('71', plain,
% 2.24/2.40      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('72', plain, (((sk_D_4 @ sk_C_3 @ sk_B) = (k1_xboole_0))),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 2.24/2.40  thf('73', plain,
% 2.24/2.40      (![X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 2.24/2.40         (~ (r2_hidden @ (k4_tarski @ X35 @ (sk_D_4 @ X33 @ X31)) @ X33)
% 2.24/2.40          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 2.24/2.40          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.24/2.40      inference('cnf', [status(esa)], [t23_relset_1])).
% 2.24/2.40  thf('74', plain,
% 2.24/2.40      (![X0 : $i, X1 : $i]:
% 2.24/2.40         (~ (r2_hidden @ (k4_tarski @ X0 @ k1_xboole_0) @ sk_C_3)
% 2.24/2.40          | ~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.24/2.40          | ((k2_relset_1 @ X1 @ sk_B @ sk_C_3) = (sk_B)))),
% 2.24/2.40      inference('sup-', [status(thm)], ['72', '73'])).
% 2.24/2.40  thf('75', plain,
% 2.24/2.40      (![X0 : $i]:
% 2.24/2.40         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))
% 2.24/2.40          | ~ (r2_hidden @ (k4_tarski @ X0 @ k1_xboole_0) @ sk_C_3))),
% 2.24/2.40      inference('sup-', [status(thm)], ['71', '74'])).
% 2.24/2.40  thf('76', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) != (sk_B))),
% 2.24/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.40  thf('77', plain,
% 2.24/2.40      (![X0 : $i]: ~ (r2_hidden @ (k4_tarski @ X0 @ k1_xboole_0) @ sk_C_3)),
% 2.24/2.40      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 2.24/2.40  thf('78', plain, ($false), inference('sup-', [status(thm)], ['70', '77'])).
% 2.24/2.40  
% 2.24/2.40  % SZS output end Refutation
% 2.24/2.40  
% 2.24/2.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
