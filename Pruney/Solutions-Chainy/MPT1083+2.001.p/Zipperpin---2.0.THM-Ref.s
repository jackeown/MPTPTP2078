%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rMfQk69e1y

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 216 expanded)
%              Number of leaves         :   40 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  791 (2988 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t200_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v5_relat_1 @ C @ A )
                & ( v1_funct_1 @ C ) )
             => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) )
                = ( k1_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_funct_2 @ B @ A @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v5_relat_1 @ C @ A )
                  & ( v1_funct_1 @ C ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) )
                  = ( k1_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t200_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_0 @ D @ C @ B @ A ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ X37 )
       != X36 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X37 @ X38 @ X36 ) @ X37 @ X38 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ( zip_tseitin_1 @ X37 @ X38 @ ( k1_relat_1 @ X37 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X37 @ X38 @ ( k1_relat_1 @ X37 ) ) @ X37 @ X38 @ ( k1_relat_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X8 ) @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v5_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ X2 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( zip_tseitin_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( zip_tseitin_1 @ sk_C @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_C @ X0 @ ( k1_relat_1 @ sk_C ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_D @ sk_C @ X0 @ ( k1_relat_1 @ sk_C ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X30 @ X29 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_C @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_C @ X0 @ ( k1_relat_1 @ sk_C ) ) @ sk_C @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ( zip_tseitin_1 @ X37 @ X38 @ ( k1_relat_1 @ X37 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X37 @ X38 @ ( k1_relat_1 @ X37 ) ) @ X37 @ X38 @ ( k1_relat_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    zip_tseitin_1 @ sk_C @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( zip_tseitin_1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( ( k8_relset_1 @ X26 @ X28 @ X27 @ X28 )
        = X26 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('24',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    zip_tseitin_1 @ sk_C @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['19'])).

thf('29',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( zip_tseitin_1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27','30','31'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k10_relat_1 @ X5 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('34',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['48','49'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['52','53','56'])).

thf('58',plain,(
    ( k10_relat_1 @ sk_C @ sk_A )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','58'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rMfQk69e1y
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 88 iterations in 0.059s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(t200_funct_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.21/0.52                 ( v1_funct_1 @ C ) ) =>
% 0.21/0.52               ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) = ( k1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.21/0.52                    ( v1_funct_1 @ C ) ) =>
% 0.21/0.52                  ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) =
% 0.21/0.52                    ( k1_relat_1 @ C ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t200_funct_2])).
% 0.21/0.52  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t5_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.21/0.52       ( ( ( ![D:$i]:
% 0.21/0.52             ( ( r2_hidden @ D @ A ) =>
% 0.21/0.52               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.21/0.52           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.21/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_1, axiom,
% 0.21/0.52    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.21/0.52       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32) | (r2_hidden @ X29 @ X32))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_3, axiom,
% 0.21/0.52    (![C:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.52       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_5, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.52       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.52           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 0.21/0.52         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.52         (((k1_relat_1 @ X37) != (X36))
% 0.21/0.52          | ~ (zip_tseitin_0 @ (sk_D @ X37 @ X38 @ X36) @ X37 @ X38 @ X36)
% 0.21/0.52          | (zip_tseitin_1 @ X37 @ X38 @ X36)
% 0.21/0.52          | ~ (v1_funct_1 @ X37)
% 0.21/0.52          | ~ (v1_relat_1 @ X37))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X37 : $i, X38 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X37)
% 0.21/0.52          | ~ (v1_funct_1 @ X37)
% 0.21/0.52          | (zip_tseitin_1 @ X37 @ X38 @ (k1_relat_1 @ X37))
% 0.21/0.52          | ~ (zip_tseitin_0 @ (sk_D @ X37 @ X38 @ (k1_relat_1 @ X37)) @ X37 @ 
% 0.21/0.52               X38 @ (k1_relat_1 @ X37)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_D @ X0 @ X1 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.21/0.52          | (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.52  thf(t172_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.52           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ X9 @ X8) @ X10)
% 0.21/0.52          | ~ (v1_funct_1 @ X9)
% 0.21/0.52          | ~ (v5_relat_1 @ X9 @ X10)
% 0.21/0.52          | ~ (v1_relat_1 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v5_relat_1 @ X0 @ X2)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k1_funct_1 @ X0 @ (sk_D @ X0 @ X1 @ (k1_relat_1 @ X0))) @ X2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((r2_hidden @ 
% 0.21/0.52           (k1_funct_1 @ X0 @ (sk_D @ X0 @ X1 @ (k1_relat_1 @ X0))) @ X2)
% 0.21/0.52          | ~ (v5_relat_1 @ X0 @ X2)
% 0.21/0.52          | (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ sk_C)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52          | (zip_tseitin_1 @ sk_C @ X0 @ (k1_relat_1 @ sk_C))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k1_funct_1 @ sk_C @ (sk_D @ sk_C @ X0 @ (k1_relat_1 @ sk_C))) @ 
% 0.21/0.52             sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '8'])).
% 0.21/0.52  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((zip_tseitin_1 @ sk_C @ X0 @ (k1_relat_1 @ sk_C))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k1_funct_1 @ sk_C @ (sk_D @ sk_C @ X0 @ (k1_relat_1 @ sk_C))) @ 
% 0.21/0.52             sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.21/0.52          | ~ (r2_hidden @ (k1_funct_1 @ X30 @ X29) @ X31))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((zip_tseitin_1 @ sk_C @ X0 @ (k1_relat_1 @ sk_C))
% 0.21/0.52          | (zip_tseitin_0 @ (sk_D @ sk_C @ X0 @ (k1_relat_1 @ sk_C)) @ sk_C @ 
% 0.21/0.52             sk_A @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X37 : $i, X38 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X37)
% 0.21/0.52          | ~ (v1_funct_1 @ X37)
% 0.21/0.52          | (zip_tseitin_1 @ X37 @ X38 @ (k1_relat_1 @ X37))
% 0.21/0.52          | ~ (zip_tseitin_0 @ (sk_D @ X37 @ X38 @ (k1_relat_1 @ X37)) @ X37 @ 
% 0.21/0.52               X38 @ (k1_relat_1 @ X37)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((zip_tseitin_1 @ sk_C @ sk_A @ (k1_relat_1 @ sk_C))
% 0.21/0.52        | (zip_tseitin_1 @ sk_C @ sk_A @ (k1_relat_1 @ sk_C))
% 0.21/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((zip_tseitin_1 @ sk_C @ sk_A @ (k1_relat_1 @ sk_C))
% 0.21/0.52        | (zip_tseitin_1 @ sk_C @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.52  thf('20', plain, ((zip_tseitin_1 @ sk_C @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.21/0.52          | ~ (zip_tseitin_1 @ X33 @ X34 @ X35))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf(t48_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.52         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.52         (((X28) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_funct_1 @ X27)
% 0.21/0.52          | ~ (v1_funct_2 @ X27 @ X26 @ X28)
% 0.21/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 0.21/0.52          | ((k8_relset_1 @ X26 @ X28 @ X27 @ X28) = (X26)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ sk_A)
% 0.21/0.52          = (k1_relat_1 @ sk_C))
% 0.21/0.52        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_A)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.21/0.52          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.21/0.52           = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain, ((zip_tseitin_1 @ sk_C @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.52         ((v1_funct_2 @ X33 @ X35 @ X34) | ~ (zip_tseitin_1 @ X33 @ X34 @ X35))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('30', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '27', '30', '31'])).
% 0.21/0.52  thf(t182_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.52             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X4)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.21/0.52              = (k10_relat_1 @ X5 @ (k1_relat_1 @ X4)))
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.52          | (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf(fc6_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.52  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '36', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc5_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.52             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.52          | (v1_partfun1 @ X18 @ X19)
% 0.21/0.52          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.21/0.52          | ~ (v1_funct_1 @ X18)
% 0.21/0.52          | (v1_xboole_0 @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.52        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('48', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.52  thf('49', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('50', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf(d4_partfun1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.52       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (~ (v1_partfun1 @ X25 @ X24)
% 0.21/0.52          | ((k1_relat_1 @ X25) = (X24))
% 0.21/0.52          | ~ (v4_relat_1 @ X25 @ X24)
% 0.21/0.52          | ~ (v1_relat_1 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.52        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.52        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         ((v4_relat_1 @ X11 @ X12)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.52  thf('56', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['52', '53', '56'])).
% 0.21/0.52  thf('58', plain, (((k10_relat_1 @ sk_C @ sk_A) != (k1_relat_1 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '57'])).
% 0.21/0.52  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['32', '58'])).
% 0.21/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.52  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('61', plain, ($false),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '59', '60'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
