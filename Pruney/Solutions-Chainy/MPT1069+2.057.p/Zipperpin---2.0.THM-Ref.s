%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.owZOTndQdK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:08 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 269 expanded)
%              Number of leaves         :   49 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          : 1358 (5469 expanded)
%              Number of equality atoms :   65 ( 232 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(t186_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ( v5_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','21'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ( sk_B
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ) )).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X36 @ X37 @ X35 @ X38 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D @ X0 ) @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D @ X0 ) @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r1_tarski @ sk_C @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','51'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C = X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['52','62'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v5_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['5','69'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('71',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( ( k7_partfun1 @ X34 @ X33 @ X32 )
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['72','77','78'])).

thf('80',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','79'])).

thf('81',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X40 @ X41 @ X44 @ X39 @ X43 ) @ X42 )
        = ( k1_funct_1 @ X43 @ ( k1_funct_1 @ X39 @ X42 ) ) )
      | ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X40 @ X41 @ X39 ) @ ( k1_relset_1 @ X41 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('88',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['82','99'])).

thf('101',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['81','100'])).

thf('102',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','101'])).

thf('103',plain,(
    v1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('105',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.owZOTndQdK
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.91/2.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.91/2.19  % Solved by: fo/fo7.sh
% 1.91/2.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.19  % done 2023 iterations in 1.733s
% 1.91/2.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.91/2.19  % SZS output start Refutation
% 1.91/2.19  thf(sk_E_type, type, sk_E: $i).
% 1.91/2.19  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.91/2.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.91/2.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.91/2.19  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.91/2.19  thf(sk_C_type, type, sk_C: $i).
% 1.91/2.19  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.91/2.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.91/2.19  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 1.91/2.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.91/2.19  thf(sk_D_type, type, sk_D: $i).
% 1.91/2.19  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.91/2.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.91/2.19  thf(sk_F_type, type, sk_F: $i).
% 1.91/2.19  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.91/2.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.91/2.19  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.91/2.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.91/2.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.91/2.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.91/2.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.91/2.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.91/2.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.91/2.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.91/2.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.91/2.19  thf(sk_B_type, type, sk_B: $i).
% 1.91/2.19  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 1.91/2.19  thf(t186_funct_2, conjecture,
% 1.91/2.19    (![A:$i,B:$i,C:$i]:
% 1.91/2.19     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.91/2.19       ( ![D:$i]:
% 1.91/2.19         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.91/2.19             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.91/2.19           ( ![E:$i]:
% 1.91/2.19             ( ( ( v1_funct_1 @ E ) & 
% 1.91/2.19                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.91/2.19               ( ![F:$i]:
% 1.91/2.19                 ( ( m1_subset_1 @ F @ B ) =>
% 1.91/2.19                   ( ( r1_tarski @
% 1.91/2.19                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.91/2.19                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.91/2.19                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.91/2.19                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.91/2.19                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.19  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.19    (~( ![A:$i,B:$i,C:$i]:
% 1.91/2.19        ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.91/2.19          ( ![D:$i]:
% 1.91/2.19            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.91/2.19                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.91/2.19              ( ![E:$i]:
% 1.91/2.19                ( ( ( v1_funct_1 @ E ) & 
% 1.91/2.19                    ( m1_subset_1 @
% 1.91/2.19                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.91/2.19                  ( ![F:$i]:
% 1.91/2.19                    ( ( m1_subset_1 @ F @ B ) =>
% 1.91/2.19                      ( ( r1_tarski @
% 1.91/2.19                          ( k2_relset_1 @ B @ C @ D ) @ 
% 1.91/2.19                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.91/2.19                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.91/2.19                          ( ( k1_funct_1 @
% 1.91/2.19                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.91/2.19                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.91/2.19    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 1.91/2.19  thf('0', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf(cc2_relset_1, axiom,
% 1.91/2.19    (![A:$i,B:$i,C:$i]:
% 1.91/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.19       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.91/2.19  thf('1', plain,
% 1.91/2.19      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.91/2.19         ((v5_relat_1 @ X15 @ X17)
% 1.91/2.19          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.91/2.19      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.91/2.19  thf('2', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 1.91/2.19      inference('sup-', [status(thm)], ['0', '1'])).
% 1.91/2.19  thf('3', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf(t2_subset, axiom,
% 1.91/2.19    (![A:$i,B:$i]:
% 1.91/2.19     ( ( m1_subset_1 @ A @ B ) =>
% 1.91/2.19       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.91/2.19  thf('4', plain,
% 1.91/2.19      (![X2 : $i, X3 : $i]:
% 1.91/2.19         ((r2_hidden @ X2 @ X3)
% 1.91/2.19          | (v1_xboole_0 @ X3)
% 1.91/2.19          | ~ (m1_subset_1 @ X2 @ X3))),
% 1.91/2.19      inference('cnf', [status(esa)], [t2_subset])).
% 1.91/2.19  thf('5', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['3', '4'])).
% 1.91/2.19  thf('6', plain,
% 1.91/2.19      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 1.91/2.19        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('7', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf(redefinition_k1_relset_1, axiom,
% 1.91/2.19    (![A:$i,B:$i,C:$i]:
% 1.91/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.91/2.19  thf('8', plain,
% 1.91/2.19      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.91/2.19         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.91/2.19          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.91/2.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.91/2.19  thf('9', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.91/2.19      inference('sup-', [status(thm)], ['7', '8'])).
% 1.91/2.19  thf('10', plain,
% 1.91/2.19      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.91/2.19      inference('demod', [status(thm)], ['6', '9'])).
% 1.91/2.19  thf('11', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf(redefinition_k2_relset_1, axiom,
% 1.91/2.19    (![A:$i,B:$i,C:$i]:
% 1.91/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.19       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.91/2.19  thf('12', plain,
% 1.91/2.19      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.91/2.19         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.91/2.19          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.91/2.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.91/2.19  thf('13', plain,
% 1.91/2.19      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.91/2.19      inference('sup-', [status(thm)], ['11', '12'])).
% 1.91/2.19  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.91/2.19      inference('demod', [status(thm)], ['10', '13'])).
% 1.91/2.19  thf(d19_relat_1, axiom,
% 1.91/2.19    (![A:$i,B:$i]:
% 1.91/2.19     ( ( v1_relat_1 @ B ) =>
% 1.91/2.19       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.91/2.19  thf('15', plain,
% 1.91/2.19      (![X6 : $i, X7 : $i]:
% 1.91/2.19         (~ (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 1.91/2.19          | (v5_relat_1 @ X6 @ X7)
% 1.91/2.19          | ~ (v1_relat_1 @ X6))),
% 1.91/2.19      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.91/2.19  thf('16', plain,
% 1.91/2.19      ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E)))),
% 1.91/2.19      inference('sup-', [status(thm)], ['14', '15'])).
% 1.91/2.19  thf('17', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf(cc2_relat_1, axiom,
% 1.91/2.19    (![A:$i]:
% 1.91/2.19     ( ( v1_relat_1 @ A ) =>
% 1.91/2.19       ( ![B:$i]:
% 1.91/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.91/2.19  thf('18', plain,
% 1.91/2.19      (![X4 : $i, X5 : $i]:
% 1.91/2.19         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.91/2.19          | (v1_relat_1 @ X4)
% 1.91/2.19          | ~ (v1_relat_1 @ X5))),
% 1.91/2.19      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.91/2.19  thf('19', plain,
% 1.91/2.19      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D))),
% 1.91/2.19      inference('sup-', [status(thm)], ['17', '18'])).
% 1.91/2.19  thf(fc6_relat_1, axiom,
% 1.91/2.19    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.91/2.19  thf('20', plain,
% 1.91/2.19      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 1.91/2.19      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.91/2.19  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 1.91/2.19      inference('demod', [status(thm)], ['19', '20'])).
% 1.91/2.19  thf('22', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 1.91/2.19      inference('demod', [status(thm)], ['16', '21'])).
% 1.91/2.19  thf(d1_funct_2, axiom,
% 1.91/2.19    (![A:$i,B:$i,C:$i]:
% 1.91/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.91/2.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.91/2.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.91/2.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.91/2.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.91/2.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.91/2.19  thf(zf_stmt_1, axiom,
% 1.91/2.19    (![B:$i,A:$i]:
% 1.91/2.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.91/2.19       ( zip_tseitin_0 @ B @ A ) ))).
% 1.91/2.19  thf('23', plain,
% 1.91/2.19      (![X24 : $i, X25 : $i]:
% 1.91/2.19         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.91/2.19  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.91/2.19  thf('24', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 1.91/2.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.91/2.19  thf('25', plain,
% 1.91/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.19         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.91/2.19      inference('sup+', [status(thm)], ['23', '24'])).
% 1.91/2.19  thf('26', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.91/2.19  thf(zf_stmt_3, axiom,
% 1.91/2.19    (![C:$i,B:$i,A:$i]:
% 1.91/2.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.91/2.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.91/2.19  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.91/2.19  thf(zf_stmt_5, axiom,
% 1.91/2.19    (![A:$i,B:$i,C:$i]:
% 1.91/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.91/2.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.91/2.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.91/2.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.91/2.19  thf('27', plain,
% 1.91/2.19      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.91/2.19         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.91/2.19          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.91/2.19          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.91/2.19  thf('28', plain,
% 1.91/2.19      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['26', '27'])).
% 1.91/2.19  thf('29', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         ((r1_tarski @ sk_C @ X0) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['25', '28'])).
% 1.91/2.19  thf('30', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('31', plain,
% 1.91/2.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.91/2.19         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.91/2.19          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.91/2.19          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.91/2.19  thf('32', plain,
% 1.91/2.19      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 1.91/2.19        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 1.91/2.19      inference('sup-', [status(thm)], ['30', '31'])).
% 1.91/2.19  thf('33', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('34', plain,
% 1.91/2.19      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.91/2.19         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.91/2.19          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.91/2.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.91/2.19  thf('35', plain,
% 1.91/2.19      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.91/2.19      inference('sup-', [status(thm)], ['33', '34'])).
% 1.91/2.19  thf('36', plain,
% 1.91/2.19      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 1.91/2.19      inference('demod', [status(thm)], ['32', '35'])).
% 1.91/2.19  thf('37', plain,
% 1.91/2.19      (![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 1.91/2.19      inference('sup-', [status(thm)], ['29', '36'])).
% 1.91/2.19  thf('38', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('39', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf(dt_k3_funct_2, axiom,
% 1.91/2.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.91/2.19     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.91/2.19         ( v1_funct_2 @ C @ A @ B ) & 
% 1.91/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.91/2.19         ( m1_subset_1 @ D @ A ) ) =>
% 1.91/2.19       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 1.91/2.19  thf('40', plain,
% 1.91/2.19      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.91/2.19         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.91/2.19          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.91/2.19          | ~ (v1_funct_1 @ X35)
% 1.91/2.19          | (v1_xboole_0 @ X36)
% 1.91/2.19          | ~ (m1_subset_1 @ X38 @ X36)
% 1.91/2.19          | (m1_subset_1 @ (k3_funct_2 @ X36 @ X37 @ X35 @ X38) @ X37))),
% 1.91/2.19      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 1.91/2.19  thf('41', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_C @ sk_D @ X0) @ sk_C)
% 1.91/2.19          | ~ (m1_subset_1 @ X0 @ sk_B)
% 1.91/2.19          | (v1_xboole_0 @ sk_B)
% 1.91/2.19          | ~ (v1_funct_1 @ sk_D)
% 1.91/2.19          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C))),
% 1.91/2.19      inference('sup-', [status(thm)], ['39', '40'])).
% 1.91/2.19  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('44', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_C @ sk_D @ X0) @ sk_C)
% 1.91/2.19          | ~ (m1_subset_1 @ X0 @ sk_B)
% 1.91/2.19          | (v1_xboole_0 @ sk_B))),
% 1.91/2.19      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.91/2.19  thf('45', plain,
% 1.91/2.19      (((v1_xboole_0 @ sk_B)
% 1.91/2.19        | (m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_C))),
% 1.91/2.19      inference('sup-', [status(thm)], ['38', '44'])).
% 1.91/2.19  thf('46', plain,
% 1.91/2.19      (![X2 : $i, X3 : $i]:
% 1.91/2.19         ((r2_hidden @ X2 @ X3)
% 1.91/2.19          | (v1_xboole_0 @ X3)
% 1.91/2.19          | ~ (m1_subset_1 @ X2 @ X3))),
% 1.91/2.19      inference('cnf', [status(esa)], [t2_subset])).
% 1.91/2.19  thf('47', plain,
% 1.91/2.19      (((v1_xboole_0 @ sk_B)
% 1.91/2.19        | (v1_xboole_0 @ sk_C)
% 1.91/2.19        | (r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_C))),
% 1.91/2.19      inference('sup-', [status(thm)], ['45', '46'])).
% 1.91/2.19  thf('48', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('49', plain,
% 1.91/2.19      (((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_C)
% 1.91/2.19        | (v1_xboole_0 @ sk_B))),
% 1.91/2.19      inference('clc', [status(thm)], ['47', '48'])).
% 1.91/2.19  thf(t7_ordinal1, axiom,
% 1.91/2.19    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.91/2.19  thf('50', plain,
% 1.91/2.19      (![X13 : $i, X14 : $i]:
% 1.91/2.19         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 1.91/2.19      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.91/2.19  thf('51', plain,
% 1.91/2.19      (((v1_xboole_0 @ sk_B)
% 1.91/2.19        | ~ (r1_tarski @ sk_C @ (k3_funct_2 @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 1.91/2.19      inference('sup-', [status(thm)], ['49', '50'])).
% 1.91/2.19  thf('52', plain, ((((sk_B) = (k1_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['37', '51'])).
% 1.91/2.19  thf(l13_xboole_0, axiom,
% 1.91/2.19    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.91/2.19  thf('53', plain,
% 1.91/2.19      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.91/2.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.91/2.19  thf('54', plain,
% 1.91/2.19      (![X24 : $i, X25 : $i]:
% 1.91/2.19         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.91/2.19  thf('55', plain,
% 1.91/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.19         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 1.91/2.19      inference('sup+', [status(thm)], ['53', '54'])).
% 1.91/2.19  thf('56', plain,
% 1.91/2.19      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['26', '27'])).
% 1.91/2.19  thf('57', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         (~ (v1_xboole_0 @ X0)
% 1.91/2.19          | ((sk_C) = (X0))
% 1.91/2.19          | (zip_tseitin_1 @ sk_D @ sk_C @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['55', '56'])).
% 1.91/2.19  thf('58', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('59', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         (~ (v1_xboole_0 @ X0)
% 1.91/2.19          | (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 1.91/2.19          | ~ (v1_xboole_0 @ X0))),
% 1.91/2.19      inference('sup-', [status(thm)], ['57', '58'])).
% 1.91/2.19  thf('60', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (v1_xboole_0 @ X0))),
% 1.91/2.19      inference('simplify', [status(thm)], ['59'])).
% 1.91/2.19  thf('61', plain,
% 1.91/2.19      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 1.91/2.19      inference('demod', [status(thm)], ['32', '35'])).
% 1.91/2.19  thf('62', plain,
% 1.91/2.19      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 1.91/2.19      inference('sup-', [status(thm)], ['60', '61'])).
% 1.91/2.19  thf('63', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.91/2.19      inference('clc', [status(thm)], ['52', '62'])).
% 1.91/2.19  thf(t172_funct_1, axiom,
% 1.91/2.19    (![A:$i,B:$i]:
% 1.91/2.19     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.91/2.19       ( ![C:$i]:
% 1.91/2.19         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.91/2.19           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 1.91/2.19  thf('64', plain,
% 1.91/2.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.91/2.19         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 1.91/2.19          | (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ X12)
% 1.91/2.19          | ~ (v1_funct_1 @ X11)
% 1.91/2.19          | ~ (v5_relat_1 @ X11 @ X12)
% 1.91/2.19          | ~ (v1_relat_1 @ X11))),
% 1.91/2.19      inference('cnf', [status(esa)], [t172_funct_1])).
% 1.91/2.19  thf('65', plain,
% 1.91/2.19      (![X0 : $i, X1 : $i]:
% 1.91/2.19         (~ (r2_hidden @ X0 @ sk_B)
% 1.91/2.19          | ~ (v1_relat_1 @ sk_D)
% 1.91/2.19          | ~ (v5_relat_1 @ sk_D @ X1)
% 1.91/2.19          | ~ (v1_funct_1 @ sk_D)
% 1.91/2.19          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 1.91/2.19      inference('sup-', [status(thm)], ['63', '64'])).
% 1.91/2.19  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 1.91/2.19      inference('demod', [status(thm)], ['19', '20'])).
% 1.91/2.19  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('68', plain,
% 1.91/2.19      (![X0 : $i, X1 : $i]:
% 1.91/2.19         (~ (r2_hidden @ X0 @ sk_B)
% 1.91/2.19          | ~ (v5_relat_1 @ sk_D @ X1)
% 1.91/2.19          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 1.91/2.19      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.91/2.19  thf('69', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 1.91/2.19          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['22', '68'])).
% 1.91/2.19  thf('70', plain,
% 1.91/2.19      (((v1_xboole_0 @ sk_B)
% 1.91/2.19        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 1.91/2.19      inference('sup-', [status(thm)], ['5', '69'])).
% 1.91/2.19  thf(d8_partfun1, axiom,
% 1.91/2.19    (![A:$i,B:$i]:
% 1.91/2.19     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.91/2.19       ( ![C:$i]:
% 1.91/2.19         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.91/2.19           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 1.91/2.19  thf('71', plain,
% 1.91/2.19      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.91/2.19         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 1.91/2.19          | ((k7_partfun1 @ X34 @ X33 @ X32) = (k1_funct_1 @ X33 @ X32))
% 1.91/2.19          | ~ (v1_funct_1 @ X33)
% 1.91/2.19          | ~ (v5_relat_1 @ X33 @ X34)
% 1.91/2.19          | ~ (v1_relat_1 @ X33))),
% 1.91/2.19      inference('cnf', [status(esa)], [d8_partfun1])).
% 1.91/2.19  thf('72', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         ((v1_xboole_0 @ sk_B)
% 1.91/2.19          | ~ (v1_relat_1 @ sk_E)
% 1.91/2.19          | ~ (v5_relat_1 @ sk_E @ X0)
% 1.91/2.19          | ~ (v1_funct_1 @ sk_E)
% 1.91/2.19          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.91/2.19              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 1.91/2.19      inference('sup-', [status(thm)], ['70', '71'])).
% 1.91/2.19  thf('73', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('74', plain,
% 1.91/2.19      (![X4 : $i, X5 : $i]:
% 1.91/2.19         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.91/2.19          | (v1_relat_1 @ X4)
% 1.91/2.19          | ~ (v1_relat_1 @ X5))),
% 1.91/2.19      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.91/2.19  thf('75', plain,
% 1.91/2.19      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 1.91/2.19      inference('sup-', [status(thm)], ['73', '74'])).
% 1.91/2.19  thf('76', plain,
% 1.91/2.19      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 1.91/2.19      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.91/2.19  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 1.91/2.19      inference('demod', [status(thm)], ['75', '76'])).
% 1.91/2.19  thf('78', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('79', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         ((v1_xboole_0 @ sk_B)
% 1.91/2.19          | ~ (v5_relat_1 @ sk_E @ X0)
% 1.91/2.19          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.91/2.19              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 1.91/2.19      inference('demod', [status(thm)], ['72', '77', '78'])).
% 1.91/2.19  thf('80', plain,
% 1.91/2.19      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.91/2.19          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.91/2.19        | (v1_xboole_0 @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['2', '79'])).
% 1.91/2.19  thf('81', plain,
% 1.91/2.19      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 1.91/2.19         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('82', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('83', plain,
% 1.91/2.19      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.91/2.19      inference('sup-', [status(thm)], ['7', '8'])).
% 1.91/2.19  thf('84', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf(t185_funct_2, axiom,
% 1.91/2.19    (![A:$i,B:$i,C:$i]:
% 1.91/2.19     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.91/2.19       ( ![D:$i]:
% 1.91/2.19         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.91/2.19             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.91/2.19           ( ![E:$i]:
% 1.91/2.19             ( ( ( v1_funct_1 @ E ) & 
% 1.91/2.19                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.91/2.19               ( ![F:$i]:
% 1.91/2.19                 ( ( m1_subset_1 @ F @ B ) =>
% 1.91/2.19                   ( ( r1_tarski @
% 1.91/2.19                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.91/2.19                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.91/2.19                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.91/2.19                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.91/2.19                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.19  thf('85', plain,
% 1.91/2.19      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.91/2.19         (~ (v1_funct_1 @ X39)
% 1.91/2.19          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 1.91/2.19          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.91/2.19          | ~ (m1_subset_1 @ X42 @ X40)
% 1.91/2.19          | ((k1_funct_1 @ (k8_funct_2 @ X40 @ X41 @ X44 @ X39 @ X43) @ X42)
% 1.91/2.19              = (k1_funct_1 @ X43 @ (k1_funct_1 @ X39 @ X42)))
% 1.91/2.19          | ((X40) = (k1_xboole_0))
% 1.91/2.19          | ~ (r1_tarski @ (k2_relset_1 @ X40 @ X41 @ X39) @ 
% 1.91/2.19               (k1_relset_1 @ X41 @ X44 @ X43))
% 1.91/2.19          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X44)))
% 1.91/2.19          | ~ (v1_funct_1 @ X43)
% 1.91/2.19          | (v1_xboole_0 @ X41))),
% 1.91/2.19      inference('cnf', [status(esa)], [t185_funct_2])).
% 1.91/2.19  thf('86', plain,
% 1.91/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.19         ((v1_xboole_0 @ sk_C)
% 1.91/2.19          | ~ (v1_funct_1 @ X0)
% 1.91/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.91/2.19          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 1.91/2.19               (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.91/2.19          | ((sk_B) = (k1_xboole_0))
% 1.91/2.19          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.91/2.19              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.91/2.19          | ~ (m1_subset_1 @ X2 @ sk_B)
% 1.91/2.19          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 1.91/2.19          | ~ (v1_funct_1 @ sk_D))),
% 1.91/2.19      inference('sup-', [status(thm)], ['84', '85'])).
% 1.91/2.19  thf('87', plain,
% 1.91/2.19      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.91/2.19      inference('sup-', [status(thm)], ['11', '12'])).
% 1.91/2.19  thf('88', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('90', plain,
% 1.91/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.19         ((v1_xboole_0 @ sk_C)
% 1.91/2.19          | ~ (v1_funct_1 @ X0)
% 1.91/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.91/2.19          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.91/2.19          | ((sk_B) = (k1_xboole_0))
% 1.91/2.19          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.91/2.19              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.91/2.19          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 1.91/2.19      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 1.91/2.19  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('92', plain,
% 1.91/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.19         ((v1_xboole_0 @ sk_C)
% 1.91/2.19          | ~ (v1_funct_1 @ X0)
% 1.91/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.91/2.19          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.91/2.19          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.91/2.19              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.91/2.19          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 1.91/2.19      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 1.91/2.19  thf('93', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 1.91/2.19          | ~ (m1_subset_1 @ X0 @ sk_B)
% 1.91/2.19          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 1.91/2.19              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.91/2.19          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 1.91/2.19          | ~ (v1_funct_1 @ sk_E)
% 1.91/2.19          | (v1_xboole_0 @ sk_C))),
% 1.91/2.19      inference('sup-', [status(thm)], ['83', '92'])).
% 1.91/2.19  thf('94', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.91/2.19      inference('demod', [status(thm)], ['10', '13'])).
% 1.91/2.19  thf('95', plain,
% 1.91/2.19      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('96', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('97', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         (~ (m1_subset_1 @ X0 @ sk_B)
% 1.91/2.19          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 1.91/2.19              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.91/2.19          | (v1_xboole_0 @ sk_C))),
% 1.91/2.19      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 1.91/2.19  thf('98', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('99', plain,
% 1.91/2.19      (![X0 : $i]:
% 1.91/2.19         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 1.91/2.19            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.91/2.19          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 1.91/2.19      inference('clc', [status(thm)], ['97', '98'])).
% 1.91/2.19  thf('100', plain,
% 1.91/2.19      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 1.91/2.19         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.91/2.19      inference('sup-', [status(thm)], ['82', '99'])).
% 1.91/2.19  thf('101', plain,
% 1.91/2.19      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.91/2.19         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.91/2.19      inference('demod', [status(thm)], ['81', '100'])).
% 1.91/2.19  thf('102', plain,
% 1.91/2.19      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.91/2.19          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.91/2.19        | (v1_xboole_0 @ sk_B))),
% 1.91/2.19      inference('sup-', [status(thm)], ['80', '101'])).
% 1.91/2.19  thf('103', plain, ((v1_xboole_0 @ sk_B)),
% 1.91/2.19      inference('simplify', [status(thm)], ['102'])).
% 1.91/2.19  thf('104', plain,
% 1.91/2.19      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.91/2.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.91/2.19  thf('105', plain, (((sk_B) = (k1_xboole_0))),
% 1.91/2.19      inference('sup-', [status(thm)], ['103', '104'])).
% 1.91/2.19  thf('106', plain, (((sk_B) != (k1_xboole_0))),
% 1.91/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.19  thf('107', plain, ($false),
% 1.91/2.19      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 1.91/2.19  
% 1.91/2.19  % SZS output end Refutation
% 1.91/2.19  
% 1.91/2.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
