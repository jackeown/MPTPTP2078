%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ma4E7NQ3Il

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:50 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 123 expanded)
%              Number of leaves         :   40 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  636 (1456 expanded)
%              Number of equality atoms :   36 (  64 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(o_1_1_funct_2_type,type,(
    o_1_1_funct_2: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(dt_o_1_1_funct_2,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( o_1_1_funct_2 @ A ) @ A ) )).

thf('21',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( o_1_1_funct_2 @ X31 ) @ X31 ) ),
    inference(cnf,[status(esa)],[dt_o_1_1_funct_2])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( o_1_1_funct_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( o_1_1_funct_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['17','28'])).

thf('30',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','29'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k7_partfun1 @ X30 @ X29 @ X28 )
        = ( k1_funct_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf('39',plain,
    ( ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( ( k3_funct_2 @ X33 @ X34 @ X32 @ X35 )
        = ( k1_funct_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ma4E7NQ3Il
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:19:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 328 iterations in 0.311s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.54/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.76  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.54/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.54/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.76  thf(o_1_1_funct_2_type, type, o_1_1_funct_2: $i > $i).
% 0.54/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.76  thf(t176_funct_2, conjecture,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.76           ( ![C:$i]:
% 0.54/0.76             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.76                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76               ( ![D:$i]:
% 0.54/0.76                 ( ( m1_subset_1 @ D @ A ) =>
% 0.54/0.76                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.54/0.76                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i]:
% 0.54/0.76        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.76          ( ![B:$i]:
% 0.54/0.76            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.76              ( ![C:$i]:
% 0.54/0.76                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.76                    ( m1_subset_1 @
% 0.54/0.76                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76                  ( ![D:$i]:
% 0.54/0.76                    ( ( m1_subset_1 @ D @ A ) =>
% 0.54/0.76                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.54/0.76                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc2_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.76         ((v5_relat_1 @ X14 @ X16)
% 0.54/0.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.76  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.54/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.76  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(t2_subset, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ A @ B ) =>
% 0.54/0.76       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.54/0.76  thf('4', plain,
% 0.54/0.76      (![X4 : $i, X5 : $i]:
% 0.54/0.76         ((r2_hidden @ X4 @ X5)
% 0.54/0.76          | (v1_xboole_0 @ X5)
% 0.54/0.76          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_subset])).
% 0.54/0.76  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_D @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.76  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('7', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.54/0.76      inference('clc', [status(thm)], ['5', '6'])).
% 0.54/0.76  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(d1_funct_2, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.54/0.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.54/0.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.54/0.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_1, axiom,
% 0.54/0.76    (![C:$i,B:$i,A:$i]:
% 0.54/0.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.76  thf('9', plain,
% 0.54/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.76         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.54/0.76          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.54/0.76          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.76  thf('10', plain,
% 0.54/0.76      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.54/0.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.76  thf('12', plain,
% 0.54/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.76         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.54/0.76          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.76  thf('13', plain,
% 0.54/0.76      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.54/0.76      inference('demod', [status(thm)], ['10', '13'])).
% 0.54/0.76  thf('15', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.76  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.54/0.76  thf(zf_stmt_4, axiom,
% 0.54/0.76    (![B:$i,A:$i]:
% 0.54/0.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.76       ( zip_tseitin_0 @ B @ A ) ))).
% 0.54/0.76  thf(zf_stmt_5, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.54/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.76         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.54/0.76          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.54/0.76          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.76  thf('17', plain,
% 0.54/0.76      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      (![X20 : $i, X21 : $i]:
% 0.54/0.76         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.76  thf('19', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.54/0.76      inference('sup+', [status(thm)], ['18', '19'])).
% 0.54/0.76  thf(dt_o_1_1_funct_2, axiom,
% 0.54/0.76    (![A:$i]: ( m1_subset_1 @ ( o_1_1_funct_2 @ A ) @ A ))).
% 0.54/0.76  thf('21', plain, (![X31 : $i]: (m1_subset_1 @ (o_1_1_funct_2 @ X31) @ X31)),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_o_1_1_funct_2])).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      (![X4 : $i, X5 : $i]:
% 0.54/0.76         ((r2_hidden @ X4 @ X5)
% 0.54/0.76          | (v1_xboole_0 @ X5)
% 0.54/0.76          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_subset])).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ X0) | (r2_hidden @ (o_1_1_funct_2 @ X0) @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.76  thf(t7_ordinal1, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      (![X9 : $i, X10 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.54/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (o_1_1_funct_2 @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.76  thf('26', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['20', '25'])).
% 0.54/0.76  thf('27', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('28', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.54/0.76      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.76  thf('29', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.54/0.76      inference('demod', [status(thm)], ['17', '28'])).
% 0.54/0.76  thf('30', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['14', '29'])).
% 0.54/0.76  thf(d8_partfun1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.76       ( ![C:$i]:
% 0.54/0.76         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.54/0.76           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.54/0.76  thf('31', plain,
% 0.54/0.76      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.54/0.76          | ((k7_partfun1 @ X30 @ X29 @ X28) = (k1_funct_1 @ X29 @ X28))
% 0.54/0.76          | ~ (v1_funct_1 @ X29)
% 0.54/0.76          | ~ (v5_relat_1 @ X29 @ X30)
% 0.54/0.76          | ~ (v1_relat_1 @ X29))),
% 0.54/0.76      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.54/0.76  thf('32', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X0 @ sk_A)
% 0.54/0.76          | ~ (v1_relat_1 @ sk_C)
% 0.54/0.76          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.54/0.76          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.76          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.76  thf('33', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc1_relset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.76       ( v1_relat_1 @ C ) ))).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.76         ((v1_relat_1 @ X11)
% 0.54/0.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.76  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.76  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X0 @ sk_A)
% 0.54/0.76          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.54/0.76          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['32', '35', '36'])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.54/0.76          | ~ (v5_relat_1 @ sk_C @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['7', '37'])).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      (((k7_partfun1 @ sk_B @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['2', '38'])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      (((k7_partfun1 @ sk_B @ sk_C @ sk_D)
% 0.54/0.76         != (k3_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('41', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('42', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(redefinition_k3_funct_2, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.54/0.76         ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.76         ( m1_subset_1 @ D @ A ) ) =>
% 0.54/0.76       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.54/0.76  thf('43', plain,
% 0.54/0.76      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.54/0.76          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.54/0.76          | ~ (v1_funct_1 @ X32)
% 0.54/0.76          | (v1_xboole_0 @ X33)
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ X33)
% 0.54/0.76          | ((k3_funct_2 @ X33 @ X34 @ X32 @ X35) = (k1_funct_1 @ X32 @ X35)))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.54/0.76          | (v1_xboole_0 @ sk_A)
% 0.54/0.76          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.76          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.54/0.76      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.76  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('46', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.54/0.76          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.54/0.76          | (v1_xboole_0 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.54/0.76  thf('48', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('49', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.54/0.76          | ((k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.54/0.76      inference('clc', [status(thm)], ['47', '48'])).
% 0.54/0.76  thf('50', plain,
% 0.54/0.76      (((k3_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.54/0.76      inference('sup-', [status(thm)], ['41', '49'])).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      (((k7_partfun1 @ sk_B @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 0.54/0.76      inference('demod', [status(thm)], ['40', '50'])).
% 0.54/0.76  thf('52', plain, ($false),
% 0.54/0.76      inference('simplify_reflect-', [status(thm)], ['39', '51'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.61/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
