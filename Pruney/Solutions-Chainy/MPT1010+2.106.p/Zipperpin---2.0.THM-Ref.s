%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MyekShfeeG

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 111 expanded)
%              Number of leaves         :   40 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  649 (1021 expanded)
%              Number of equality atoms :   51 (  71 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('3',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X1: $i,X4: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X4 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X21: $i,X23: $i,X25: $i,X26: $i] :
      ( ( X23
       != ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ X25 @ X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X21 ) )
      | ( X25
       != ( k1_funct_1 @ X21 @ X26 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('24',plain,(
    ! [X21: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X21 @ X26 ) @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['25','26','31'])).

thf('33',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X29 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('36',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ( X5 = X4 )
      | ( X5 = X1 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('46',plain,(
    ! [X1: $i,X4: $i,X5: $i] :
      ( ( X5 = X1 )
      | ( X5 = X4 )
      | ~ ( r2_hidden @ X5 @ ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MyekShfeeG
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:53:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 114 iterations in 0.074s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(t65_funct_2, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.53         ( m1_subset_1 @
% 0.20/0.53           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.53       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.53            ( m1_subset_1 @
% 0.20/0.53              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.53          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.53  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d1_funct_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_1, axiom,
% 0.20/0.53    (![B:$i,A:$i]:
% 0.20/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X38 : $i, X39 : $i]:
% 0.20/0.53         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_3, axiom,
% 0.20/0.53    (![C:$i,B:$i,A:$i]:
% 0.20/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.53  thf(zf_stmt_5, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.53         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.20/0.53          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.20/0.53          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.53        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.53  thf('6', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.53         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.20/0.53          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.20/0.53          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.53        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.53         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.20/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)
% 0.20/0.53         = (k1_relat_1 @ sk_D_3))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.53        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '12'])).
% 0.20/0.53  thf(t69_enumset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('14', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf(d2_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (((X2) != (X1))
% 0.20/0.53          | (r2_hidden @ X2 @ X3)
% 0.20/0.53          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X1 : $i, X4 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X4 @ X1))),
% 0.20/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.53  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['14', '16'])).
% 0.20/0.53  thf(t7_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.53  thf('19', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((~ (r1_tarski @ k1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '19'])).
% 0.20/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.53  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf('22', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf(d5_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.53               ( ?[D:$i]:
% 0.20/0.53                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.53                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X21 : $i, X23 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (((X23) != (k2_relat_1 @ X21))
% 0.20/0.53          | (r2_hidden @ X25 @ X23)
% 0.20/0.53          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X21))
% 0.20/0.53          | ((X25) != (k1_funct_1 @ X21 @ X26))
% 0.20/0.53          | ~ (v1_funct_1 @ X21)
% 0.20/0.53          | ~ (v1_relat_1 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X21 : $i, X26 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X21)
% 0.20/0.53          | ~ (v1_funct_1 @ X21)
% 0.20/0.53          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X21))
% 0.20/0.53          | (r2_hidden @ (k1_funct_1 @ X21 @ X26) @ (k2_relat_1 @ X21)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.53          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_D_3)
% 0.20/0.53          | ~ (v1_relat_1 @ sk_D_3))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.53  thf('26', plain, ((v1_funct_1 @ sk_D_3)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.20/0.53          | (v1_relat_1 @ X16)
% 0.20/0.53          | ~ (v1_relat_1 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.53        | (v1_relat_1 @ sk_D_3))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf(fc6_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('31', plain, ((v1_relat_1 @ sk_D_3)),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.53          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3)))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k2_relat_1 @ sk_D_3))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k2_relset_1 @ X29 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))
% 0.20/0.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.53         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 0.20/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D_3)
% 0.20/0.53         = (k2_relat_1 @ sk_D_3))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((m1_subset_1 @ (k2_relat_1 @ sk_D_3) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_tarski @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['36', '39'])).
% 0.20/0.53  thf(l3_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X13 @ X14)
% 0.20/0.53          | (r2_hidden @ X13 @ X15)
% 0.20/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '42'])).
% 0.20/0.53  thf('44', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X5 @ X3)
% 0.20/0.53          | ((X5) = (X4))
% 0.20/0.53          | ((X5) = (X1))
% 0.20/0.53          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X1 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (((X5) = (X1))
% 0.20/0.53          | ((X5) = (X4))
% 0.20/0.53          | ~ (r2_hidden @ X5 @ (k2_tarski @ X4 @ X1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.53  thf('49', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) = (sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '48'])).
% 0.20/0.53  thf('50', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) != (sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
