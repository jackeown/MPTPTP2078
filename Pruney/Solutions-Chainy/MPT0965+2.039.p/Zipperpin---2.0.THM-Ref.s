%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hoLLyZxqj2

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:03 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 114 expanded)
%              Number of leaves         :   44 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  584 (1005 expanded)
%              Number of equality atoms :   40 (  59 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('5',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','13','16'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X19 @ X18 ) @ X20 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','27'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['30','31'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('33',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k6_subset_1 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ ( k6_subset_1 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hoLLyZxqj2
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:08:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 83 iterations in 0.103s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.56  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.39/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.56  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.56  thf(t7_funct_2, conjecture,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.56       ( ( r2_hidden @ C @ A ) =>
% 0.39/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.56           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.56          ( ( r2_hidden @ C @ A ) =>
% 0.39/0.56            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.56              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.39/0.56  thf('0', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc2_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.56         ((v5_relat_1 @ X21 @ X23)
% 0.39/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.56  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 0.39/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.56  thf('3', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(d1_funct_2, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_1, axiom,
% 0.39/0.56    (![C:$i,B:$i,A:$i]:
% 0.39/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.56         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.39/0.56          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.39/0.56          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.39/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf(zf_stmt_2, axiom,
% 0.39/0.56    (![B:$i,A:$i]:
% 0.39/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X31 : $i, X32 : $i]:
% 0.39/0.56         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.56  thf(zf_stmt_5, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.39/0.56         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.39/0.56          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.39/0.56          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.39/0.56        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['7', '10'])).
% 0.39/0.56  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('13', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.39/0.56      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.56         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.39/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.39/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.56  thf('17', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.39/0.56      inference('demod', [status(thm)], ['6', '13', '16'])).
% 0.39/0.56  thf(t176_funct_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.56       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.39/0.56         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.39/0.56          | (m1_subset_1 @ (k1_funct_1 @ X19 @ X18) @ X20)
% 0.39/0.56          | ~ (v1_funct_1 @ X19)
% 0.39/0.56          | ~ (v5_relat_1 @ X19 @ X20)
% 0.39/0.56          | ~ (v1_relat_1 @ X19))),
% 0.39/0.56      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.39/0.56          | ~ (v1_relat_1 @ sk_D)
% 0.39/0.56          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.39/0.56          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.56          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc2_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X14 : $i, X15 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.39/0.56          | (v1_relat_1 @ X14)
% 0.39/0.56          | ~ (v1_relat_1 @ X15))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.56  thf('22', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.39/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.56  thf(fc6_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.56  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.56  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.39/0.56          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.39/0.56          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.39/0.56      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ X0)
% 0.39/0.56          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['3', '26'])).
% 0.39/0.56  thf('28', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.39/0.56      inference('sup-', [status(thm)], ['2', '27'])).
% 0.39/0.56  thf(t2_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         ((r2_hidden @ X9 @ X10)
% 0.39/0.56          | (v1_xboole_0 @ X10)
% 0.39/0.56          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.39/0.56        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.56  thf('31', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('32', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.39/0.56      inference('clc', [status(thm)], ['30', '31'])).
% 0.39/0.56  thf(t29_mcart_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ~( ( r2_hidden @ B @ A ) & 
% 0.39/0.56                 ( ![C:$i,D:$i,E:$i]:
% 0.39/0.56                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.39/0.56                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      (![X27 : $i]:
% 0.39/0.56         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.39/0.56      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.39/0.56  thf(dt_k6_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.56  thf('34', plain,
% 0.39/0.56      (![X5 : $i, X6 : $i]:
% 0.39/0.56         (m1_subset_1 @ (k6_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.39/0.56  thf(t5_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.39/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X11 @ X12)
% 0.39/0.56          | ~ (v1_xboole_0 @ X13)
% 0.39/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.56  thf('36', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k6_subset_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['33', '36'])).
% 0.39/0.56  thf(l32_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.39/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.56  thf(redefinition_k6_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.56  thf('39', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.39/0.56  thf('40', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((r1_tarski @ X0 @ X1) | ((k6_subset_1 @ X0 @ X1) != (k1_xboole_0)))),
% 0.39/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.56          | ~ (v1_xboole_0 @ X1)
% 0.39/0.56          | (r1_tarski @ X1 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['37', '40'])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X1 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.56  thf(t38_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.39/0.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.56  thf('43', plain,
% 0.39/0.56      (![X3 : $i, X4 : $i]:
% 0.39/0.56         (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X3)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.39/0.56  thf('45', plain,
% 0.39/0.56      (![X3 : $i, X4 : $i]:
% 0.39/0.56         (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ (k6_subset_1 @ X4 @ X3)))),
% 0.39/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.39/0.56  thf('46', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['42', '45'])).
% 0.39/0.56  thf('47', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['32', '46'])).
% 0.39/0.56  thf('48', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('49', plain, ($false),
% 0.39/0.56      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
