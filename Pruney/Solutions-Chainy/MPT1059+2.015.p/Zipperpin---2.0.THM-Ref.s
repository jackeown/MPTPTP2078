%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eXekXrJAAi

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:51 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 126 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  659 (1479 expanded)
%              Number of equality atoms :   36 (  64 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(o_1_1_funct_2_type,type,(
    o_1_1_funct_2: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t176_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( k7_partfun1 @ B @ C @ D )
                      = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(dt_o_1_1_funct_2,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( o_1_1_funct_2 @ A ) @ A ) )).

thf('23',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( o_1_1_funct_2 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[dt_o_1_1_funct_2])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( o_1_1_funct_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( o_1_1_funct_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['17','30'])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','31'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('33',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( ( k7_partfun1 @ X33 @ X32 @ X31 )
        = ( k1_funct_1 @ X32 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf('41',plain,
    ( ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','40'])).

thf('42',plain,(
    ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('45',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k3_funct_2 @ X36 @ X37 @ X35 @ X38 )
        = ( k1_funct_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eXekXrJAAi
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.21/0.34  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.14/1.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.14/1.36  % Solved by: fo/fo7.sh
% 1.14/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.36  % done 620 iterations in 0.910s
% 1.14/1.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.14/1.36  % SZS output start Refutation
% 1.14/1.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.14/1.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.14/1.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.36  thf(sk_D_type, type, sk_D: $i).
% 1.14/1.36  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 1.14/1.36  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.14/1.36  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.14/1.36  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.14/1.36  thf(sk_C_type, type, sk_C: $i).
% 1.14/1.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.14/1.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.14/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.14/1.36  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.14/1.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.14/1.36  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.14/1.36  thf(o_1_1_funct_2_type, type, o_1_1_funct_2: $i > $i).
% 1.14/1.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.14/1.36  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.14/1.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.14/1.36  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.14/1.36  thf(t176_funct_2, conjecture,
% 1.14/1.36    (![A:$i]:
% 1.14/1.36     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.14/1.36       ( ![B:$i]:
% 1.14/1.36         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.14/1.36           ( ![C:$i]:
% 1.14/1.36             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.14/1.36                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.14/1.36               ( ![D:$i]:
% 1.14/1.36                 ( ( m1_subset_1 @ D @ A ) =>
% 1.14/1.36                   ( ( k7_partfun1 @ B @ C @ D ) =
% 1.14/1.36                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.14/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.36    (~( ![A:$i]:
% 1.14/1.36        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.14/1.36          ( ![B:$i]:
% 1.14/1.36            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.14/1.36              ( ![C:$i]:
% 1.14/1.36                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.14/1.36                    ( m1_subset_1 @
% 1.14/1.36                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.14/1.36                  ( ![D:$i]:
% 1.14/1.36                    ( ( m1_subset_1 @ D @ A ) =>
% 1.14/1.36                      ( ( k7_partfun1 @ B @ C @ D ) =
% 1.14/1.36                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 1.14/1.36    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 1.14/1.36  thf('0', plain,
% 1.14/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf(cc2_relset_1, axiom,
% 1.14/1.36    (![A:$i,B:$i,C:$i]:
% 1.14/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.36       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.14/1.36  thf('1', plain,
% 1.14/1.36      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.14/1.36         ((v5_relat_1 @ X17 @ X19)
% 1.14/1.36          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.14/1.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.36  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 1.14/1.36      inference('sup-', [status(thm)], ['0', '1'])).
% 1.14/1.36  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf(t2_subset, axiom,
% 1.14/1.36    (![A:$i,B:$i]:
% 1.14/1.36     ( ( m1_subset_1 @ A @ B ) =>
% 1.14/1.36       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.14/1.36  thf('4', plain,
% 1.14/1.36      (![X4 : $i, X5 : $i]:
% 1.14/1.36         ((r2_hidden @ X4 @ X5)
% 1.14/1.36          | (v1_xboole_0 @ X5)
% 1.14/1.36          | ~ (m1_subset_1 @ X4 @ X5))),
% 1.14/1.36      inference('cnf', [status(esa)], [t2_subset])).
% 1.14/1.36  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_D @ sk_A))),
% 1.14/1.36      inference('sup-', [status(thm)], ['3', '4'])).
% 1.14/1.36  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf('7', plain, ((r2_hidden @ sk_D @ sk_A)),
% 1.14/1.36      inference('clc', [status(thm)], ['5', '6'])).
% 1.14/1.36  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf(d1_funct_2, axiom,
% 1.14/1.36    (![A:$i,B:$i,C:$i]:
% 1.14/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.36       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.14/1.36           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.14/1.36             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.14/1.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.14/1.36           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.14/1.36             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.14/1.36  thf(zf_stmt_1, axiom,
% 1.14/1.36    (![C:$i,B:$i,A:$i]:
% 1.14/1.36     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.14/1.36       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.14/1.36  thf('9', plain,
% 1.14/1.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.14/1.36         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.14/1.36          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 1.14/1.36          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.14/1.36  thf('10', plain,
% 1.14/1.36      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.14/1.36        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.14/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.14/1.36  thf('11', plain,
% 1.14/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf(redefinition_k1_relset_1, axiom,
% 1.14/1.36    (![A:$i,B:$i,C:$i]:
% 1.14/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.36       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.14/1.36  thf('12', plain,
% 1.14/1.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.14/1.36         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 1.14/1.36          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.14/1.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.14/1.36  thf('13', plain,
% 1.14/1.36      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.14/1.36      inference('sup-', [status(thm)], ['11', '12'])).
% 1.14/1.36  thf('14', plain,
% 1.14/1.36      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.14/1.36      inference('demod', [status(thm)], ['10', '13'])).
% 1.14/1.36  thf('15', plain,
% 1.14/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.14/1.36  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.14/1.36  thf(zf_stmt_4, axiom,
% 1.14/1.36    (![B:$i,A:$i]:
% 1.14/1.36     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.14/1.36       ( zip_tseitin_0 @ B @ A ) ))).
% 1.14/1.36  thf(zf_stmt_5, axiom,
% 1.14/1.36    (![A:$i,B:$i,C:$i]:
% 1.14/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.36       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.14/1.36         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.14/1.36           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.14/1.36             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.14/1.36  thf('16', plain,
% 1.14/1.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.14/1.36         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.14/1.36          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.14/1.36          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.14/1.36  thf('17', plain,
% 1.14/1.36      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.14/1.36      inference('sup-', [status(thm)], ['15', '16'])).
% 1.14/1.36  thf('18', plain,
% 1.14/1.36      (![X23 : $i, X24 : $i]:
% 1.14/1.36         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.14/1.36  thf(t4_subset_1, axiom,
% 1.14/1.36    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.14/1.36  thf('19', plain,
% 1.14/1.36      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 1.14/1.36      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.14/1.36  thf('20', plain,
% 1.14/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.36         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.14/1.36      inference('sup+', [status(thm)], ['18', '19'])).
% 1.14/1.36  thf(t3_subset, axiom,
% 1.14/1.36    (![A:$i,B:$i]:
% 1.14/1.36     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.14/1.36  thf('21', plain,
% 1.14/1.36      (![X6 : $i, X7 : $i]:
% 1.14/1.36         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.14/1.36      inference('cnf', [status(esa)], [t3_subset])).
% 1.14/1.36  thf('22', plain,
% 1.14/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.36         ((zip_tseitin_0 @ X1 @ X2) | (r1_tarski @ X1 @ X0))),
% 1.14/1.36      inference('sup-', [status(thm)], ['20', '21'])).
% 1.14/1.36  thf(dt_o_1_1_funct_2, axiom,
% 1.14/1.36    (![A:$i]: ( m1_subset_1 @ ( o_1_1_funct_2 @ A ) @ A ))).
% 1.14/1.36  thf('23', plain, (![X34 : $i]: (m1_subset_1 @ (o_1_1_funct_2 @ X34) @ X34)),
% 1.14/1.36      inference('cnf', [status(esa)], [dt_o_1_1_funct_2])).
% 1.14/1.36  thf('24', plain,
% 1.14/1.36      (![X4 : $i, X5 : $i]:
% 1.14/1.36         ((r2_hidden @ X4 @ X5)
% 1.14/1.36          | (v1_xboole_0 @ X5)
% 1.14/1.36          | ~ (m1_subset_1 @ X4 @ X5))),
% 1.14/1.36      inference('cnf', [status(esa)], [t2_subset])).
% 1.14/1.36  thf('25', plain,
% 1.14/1.36      (![X0 : $i]:
% 1.14/1.36         ((v1_xboole_0 @ X0) | (r2_hidden @ (o_1_1_funct_2 @ X0) @ X0))),
% 1.14/1.36      inference('sup-', [status(thm)], ['23', '24'])).
% 1.14/1.36  thf(t7_ordinal1, axiom,
% 1.14/1.36    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.14/1.36  thf('26', plain,
% 1.14/1.36      (![X12 : $i, X13 : $i]:
% 1.14/1.36         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 1.14/1.36      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.14/1.36  thf('27', plain,
% 1.14/1.36      (![X0 : $i]:
% 1.14/1.36         ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (o_1_1_funct_2 @ X0)))),
% 1.14/1.36      inference('sup-', [status(thm)], ['25', '26'])).
% 1.14/1.36  thf('28', plain,
% 1.14/1.36      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 1.14/1.36      inference('sup-', [status(thm)], ['22', '27'])).
% 1.14/1.36  thf('29', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf('30', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 1.14/1.36      inference('sup-', [status(thm)], ['28', '29'])).
% 1.14/1.36  thf('31', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.14/1.36      inference('demod', [status(thm)], ['17', '30'])).
% 1.14/1.36  thf('32', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.14/1.36      inference('demod', [status(thm)], ['14', '31'])).
% 1.14/1.36  thf(d8_partfun1, axiom,
% 1.14/1.36    (![A:$i,B:$i]:
% 1.14/1.36     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.36       ( ![C:$i]:
% 1.14/1.36         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.14/1.36           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 1.14/1.36  thf('33', plain,
% 1.14/1.36      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.14/1.36         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 1.14/1.36          | ((k7_partfun1 @ X33 @ X32 @ X31) = (k1_funct_1 @ X32 @ X31))
% 1.14/1.36          | ~ (v1_funct_1 @ X32)
% 1.14/1.36          | ~ (v5_relat_1 @ X32 @ X33)
% 1.14/1.36          | ~ (v1_relat_1 @ X32))),
% 1.14/1.36      inference('cnf', [status(esa)], [d8_partfun1])).
% 1.14/1.36  thf('34', plain,
% 1.14/1.36      (![X0 : $i, X1 : $i]:
% 1.14/1.36         (~ (r2_hidden @ X0 @ sk_A)
% 1.14/1.36          | ~ (v1_relat_1 @ sk_C)
% 1.14/1.36          | ~ (v5_relat_1 @ sk_C @ X1)
% 1.14/1.36          | ~ (v1_funct_1 @ sk_C)
% 1.14/1.36          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 1.14/1.36      inference('sup-', [status(thm)], ['32', '33'])).
% 1.14/1.36  thf('35', plain,
% 1.14/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf(cc1_relset_1, axiom,
% 1.14/1.36    (![A:$i,B:$i,C:$i]:
% 1.14/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.36       ( v1_relat_1 @ C ) ))).
% 1.14/1.36  thf('36', plain,
% 1.14/1.36      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.14/1.36         ((v1_relat_1 @ X14)
% 1.14/1.36          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.14/1.36      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.14/1.36  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 1.14/1.36      inference('sup-', [status(thm)], ['35', '36'])).
% 1.14/1.36  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf('39', plain,
% 1.14/1.36      (![X0 : $i, X1 : $i]:
% 1.14/1.36         (~ (r2_hidden @ X0 @ sk_A)
% 1.14/1.36          | ~ (v5_relat_1 @ sk_C @ X1)
% 1.14/1.36          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 1.14/1.36      inference('demod', [status(thm)], ['34', '37', '38'])).
% 1.14/1.36  thf('40', plain,
% 1.14/1.36      (![X0 : $i]:
% 1.14/1.36         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 1.14/1.36          | ~ (v5_relat_1 @ sk_C @ X0))),
% 1.14/1.36      inference('sup-', [status(thm)], ['7', '39'])).
% 1.14/1.36  thf('41', plain,
% 1.14/1.36      (((k7_partfun1 @ sk_B @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 1.14/1.36      inference('sup-', [status(thm)], ['2', '40'])).
% 1.14/1.36  thf('42', plain,
% 1.14/1.36      (((k7_partfun1 @ sk_B @ sk_C @ sk_D)
% 1.14/1.36         != (k3_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf('43', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf('44', plain,
% 1.14/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf(redefinition_k3_funct_2, axiom,
% 1.14/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.36     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.14/1.36         ( v1_funct_2 @ C @ A @ B ) & 
% 1.14/1.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.14/1.36         ( m1_subset_1 @ D @ A ) ) =>
% 1.14/1.36       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.14/1.36  thf('45', plain,
% 1.14/1.36      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.14/1.36         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.14/1.36          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.14/1.36          | ~ (v1_funct_1 @ X35)
% 1.14/1.36          | (v1_xboole_0 @ X36)
% 1.14/1.36          | ~ (m1_subset_1 @ X38 @ X36)
% 1.14/1.36          | ((k3_funct_2 @ X36 @ X37 @ X35 @ X38) = (k1_funct_1 @ X35 @ X38)))),
% 1.14/1.36      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.14/1.36  thf('46', plain,
% 1.14/1.36      (![X0 : $i]:
% 1.14/1.36         (((k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 1.14/1.36          | ~ (m1_subset_1 @ X0 @ sk_A)
% 1.14/1.36          | (v1_xboole_0 @ sk_A)
% 1.14/1.36          | ~ (v1_funct_1 @ sk_C)
% 1.14/1.36          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 1.14/1.36      inference('sup-', [status(thm)], ['44', '45'])).
% 1.14/1.36  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf('49', plain,
% 1.14/1.36      (![X0 : $i]:
% 1.14/1.36         (((k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 1.14/1.36          | ~ (m1_subset_1 @ X0 @ sk_A)
% 1.14/1.36          | (v1_xboole_0 @ sk_A))),
% 1.14/1.36      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.14/1.36  thf('50', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.14/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.36  thf('51', plain,
% 1.14/1.36      (![X0 : $i]:
% 1.14/1.36         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.14/1.36          | ((k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 1.14/1.36      inference('clc', [status(thm)], ['49', '50'])).
% 1.14/1.36  thf('52', plain,
% 1.14/1.36      (((k3_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 1.14/1.36      inference('sup-', [status(thm)], ['43', '51'])).
% 1.14/1.36  thf('53', plain,
% 1.14/1.36      (((k7_partfun1 @ sk_B @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 1.14/1.36      inference('demod', [status(thm)], ['42', '52'])).
% 1.14/1.36  thf('54', plain, ($false),
% 1.14/1.36      inference('simplify_reflect-', [status(thm)], ['41', '53'])).
% 1.14/1.36  
% 1.14/1.36  % SZS output end Refutation
% 1.14/1.36  
% 1.23/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
