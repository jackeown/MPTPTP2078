%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.01YUdkXMJx

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:59 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 476 expanded)
%              Number of leaves         :   41 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          :  709 (6469 expanded)
%              Number of equality atoms :   54 ( 344 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k11_relat_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k11_relat_1 @ X24 @ X23 )
        = ( k1_tarski @ ( k1_funct_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k11_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k11_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ X16 @ ( k1_tarski @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('40',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','38','39','40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ sk_D @ X0 ) )
      | ( ( k2_relat_1 @ sk_D )
        = ( k9_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['49','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['21','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.01YUdkXMJx
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.58/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.83  % Solved by: fo/fo7.sh
% 0.58/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.83  % done 539 iterations in 0.394s
% 0.58/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.83  % SZS output start Refutation
% 0.58/0.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.83  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.58/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.83  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.58/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.83  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.83  thf(t64_funct_2, conjecture,
% 0.58/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.83     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.83         ( m1_subset_1 @
% 0.58/0.83           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.83       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.83         ( r1_tarski @
% 0.58/0.83           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.58/0.83           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.83        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.83            ( m1_subset_1 @
% 0.58/0.83              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.83          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.83            ( r1_tarski @
% 0.58/0.83              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.58/0.83              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.58/0.83    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.58/0.83  thf('0', plain,
% 0.58/0.83      (~ (r1_tarski @ 
% 0.58/0.83          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.58/0.83          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(d1_funct_2, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.83           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.83             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.83         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.83           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.83             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_1, axiom,
% 0.58/0.83    (![C:$i,B:$i,A:$i]:
% 0.58/0.83     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.83       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.83  thf('2', plain,
% 0.58/0.83      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.58/0.83         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.58/0.83          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.58/0.83          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.83  thf('3', plain,
% 0.58/0.83      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.58/0.83        | ((k1_tarski @ sk_A)
% 0.58/0.83            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.83  thf(zf_stmt_2, axiom,
% 0.58/0.83    (![B:$i,A:$i]:
% 0.58/0.83     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.83       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.83  thf('4', plain,
% 0.58/0.83      (![X35 : $i, X36 : $i]:
% 0.58/0.83         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.83  thf('5', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_D @ 
% 0.58/0.83        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.83  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.83  thf(zf_stmt_5, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.83         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.83           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.83             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.83  thf('6', plain,
% 0.58/0.83      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.58/0.83         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.58/0.83          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.58/0.83          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.83  thf('7', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.58/0.83        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.83  thf('8', plain,
% 0.58/0.83      ((((sk_B) = (k1_xboole_0))
% 0.58/0.83        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['4', '7'])).
% 0.58/0.83  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.58/0.83      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.58/0.83  thf('11', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_D @ 
% 0.58/0.83        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.83  thf('12', plain,
% 0.58/0.83      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.83         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.58/0.83          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.58/0.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.83  thf('13', plain,
% 0.58/0.83      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.58/0.83      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.83  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.58/0.83      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.58/0.83  thf('15', plain,
% 0.58/0.83      (~ (r1_tarski @ 
% 0.58/0.83          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.58/0.83          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.58/0.83      inference('demod', [status(thm)], ['0', '14'])).
% 0.58/0.83  thf('16', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_D @ 
% 0.58/0.83        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.58/0.83      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.58/0.83  thf('18', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_D @ 
% 0.58/0.83        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.58/0.83      inference('demod', [status(thm)], ['16', '17'])).
% 0.58/0.83  thf(redefinition_k7_relset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.58/0.83  thf('19', plain,
% 0.58/0.83      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.58/0.83          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.58/0.83      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.58/0.83  thf('20', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.58/0.83           = (k9_relat_1 @ sk_D @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.83  thf('21', plain,
% 0.58/0.83      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.58/0.83          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.58/0.83      inference('demod', [status(thm)], ['15', '20'])).
% 0.58/0.83  thf(t144_relat_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( v1_relat_1 @ B ) =>
% 0.58/0.83       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.58/0.83  thf('22', plain,
% 0.58/0.83      (![X18 : $i, X19 : $i]:
% 0.58/0.83         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 0.58/0.83          | ~ (v1_relat_1 @ X18))),
% 0.58/0.83      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.58/0.83  thf(t205_relat_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( v1_relat_1 @ B ) =>
% 0.58/0.83       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.58/0.83         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.58/0.83  thf('23', plain,
% 0.58/0.83      (![X21 : $i, X22 : $i]:
% 0.58/0.83         (((k11_relat_1 @ X21 @ X22) = (k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.58/0.83          | ~ (v1_relat_1 @ X21))),
% 0.58/0.83      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.58/0.83  thf(t117_funct_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.83       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.58/0.83         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.58/0.83  thf('24', plain,
% 0.58/0.83      (![X23 : $i, X24 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.58/0.83          | ((k11_relat_1 @ X24 @ X23) = (k1_tarski @ (k1_funct_1 @ X24 @ X23)))
% 0.58/0.83          | ~ (v1_funct_1 @ X24)
% 0.58/0.83          | ~ (v1_relat_1 @ X24))),
% 0.58/0.83      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.58/0.83  thf('25', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (~ (v1_relat_1 @ X0)
% 0.58/0.83          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.58/0.83          | ~ (v1_relat_1 @ X0)
% 0.58/0.83          | ~ (v1_funct_1 @ X0)
% 0.58/0.83          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.83  thf('26', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1)))
% 0.58/0.83          | ~ (v1_funct_1 @ X0)
% 0.58/0.83          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.58/0.83          | ~ (v1_relat_1 @ X0))),
% 0.58/0.83      inference('simplify', [status(thm)], ['25'])).
% 0.58/0.83  thf('27', plain,
% 0.58/0.83      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.58/0.83          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.58/0.83      inference('demod', [status(thm)], ['15', '20'])).
% 0.58/0.83  thf('28', plain,
% 0.58/0.83      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k11_relat_1 @ sk_D @ sk_A))
% 0.58/0.83        | ~ (v1_relat_1 @ sk_D)
% 0.58/0.83        | ((k11_relat_1 @ sk_D @ sk_A) = (k1_xboole_0))
% 0.58/0.83        | ~ (v1_funct_1 @ sk_D))),
% 0.58/0.83      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.83  thf(t146_relat_1, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( v1_relat_1 @ A ) =>
% 0.58/0.83       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.58/0.83  thf('29', plain,
% 0.58/0.83      (![X20 : $i]:
% 0.58/0.83         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 0.58/0.83          | ~ (v1_relat_1 @ X20))),
% 0.58/0.83      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.58/0.83  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.58/0.83      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.58/0.83  thf(d16_relat_1, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( v1_relat_1 @ A ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.58/0.83  thf('31', plain,
% 0.58/0.83      (![X16 : $i, X17 : $i]:
% 0.58/0.83         (((k11_relat_1 @ X16 @ X17) = (k9_relat_1 @ X16 @ (k1_tarski @ X17)))
% 0.58/0.83          | ~ (v1_relat_1 @ X16))),
% 0.58/0.83      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.58/0.83  thf('32', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D)))
% 0.58/0.83          | ~ (v1_relat_1 @ X0))),
% 0.58/0.83      inference('sup+', [status(thm)], ['30', '31'])).
% 0.58/0.83  thf('33', plain,
% 0.58/0.83      ((((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))
% 0.58/0.83        | ~ (v1_relat_1 @ sk_D)
% 0.58/0.83        | ~ (v1_relat_1 @ sk_D))),
% 0.58/0.83      inference('sup+', [status(thm)], ['29', '32'])).
% 0.58/0.83  thf('34', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_D @ 
% 0.58/0.83        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(cc1_relset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83       ( v1_relat_1 @ C ) ))).
% 0.58/0.83  thf('35', plain,
% 0.58/0.83      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.83         ((v1_relat_1 @ X25)
% 0.58/0.83          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.58/0.83      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.83  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.83  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.83  thf('38', plain, (((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))),
% 0.58/0.83      inference('demod', [status(thm)], ['33', '36', '37'])).
% 0.58/0.83  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.83  thf('40', plain, (((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))),
% 0.58/0.83      inference('demod', [status(thm)], ['33', '36', '37'])).
% 0.58/0.83  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('42', plain,
% 0.58/0.83      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.58/0.83        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.58/0.83      inference('demod', [status(thm)], ['28', '38', '39', '40', '41'])).
% 0.58/0.83  thf('43', plain,
% 0.58/0.83      ((~ (v1_relat_1 @ sk_D) | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['22', '42'])).
% 0.58/0.83  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.83  thf('45', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.83      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.83  thf('46', plain,
% 0.58/0.83      (![X18 : $i, X19 : $i]:
% 0.58/0.83         ((r1_tarski @ (k9_relat_1 @ X18 @ X19) @ (k2_relat_1 @ X18))
% 0.58/0.83          | ~ (v1_relat_1 @ X18))),
% 0.58/0.83      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.58/0.83  thf(d10_xboole_0, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.83  thf('47', plain,
% 0.58/0.83      (![X0 : $i, X2 : $i]:
% 0.58/0.83         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.83  thf('48', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (~ (v1_relat_1 @ X0)
% 0.58/0.83          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.58/0.83          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.83  thf('49', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ sk_D @ X0))
% 0.58/0.83          | ((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ X0))
% 0.58/0.83          | ~ (v1_relat_1 @ sk_D))),
% 0.58/0.83      inference('sup-', [status(thm)], ['45', '48'])).
% 0.58/0.83  thf(t4_subset_1, axiom,
% 0.58/0.83    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.83  thf('50', plain,
% 0.58/0.83      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.58/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.83  thf(t3_subset, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.83  thf('51', plain,
% 0.58/0.83      (![X10 : $i, X11 : $i]:
% 0.58/0.83         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.58/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.83  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.83  thf('53', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.83      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.83  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.83  thf('55', plain, (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_D @ X0))),
% 0.58/0.83      inference('demod', [status(thm)], ['49', '52', '53', '54'])).
% 0.58/0.83  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.83  thf('57', plain, ($false),
% 0.58/0.83      inference('demod', [status(thm)], ['21', '55', '56'])).
% 0.58/0.83  
% 0.58/0.83  % SZS output end Refutation
% 0.58/0.83  
% 0.58/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
