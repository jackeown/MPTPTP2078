%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FJG6Nodt2n

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:14 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 318 expanded)
%              Number of leaves         :   51 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          : 1063 (4113 expanded)
%              Number of equality atoms :   87 ( 278 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

thf('0',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v5_relat_1 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v5_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( zip_tseitin_3 @ B @ A )
          | ( zip_tseitin_2 @ D @ C @ A ) ) ) ) )).

thf('22',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( zip_tseitin_3 @ X62 @ X63 )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_funct_2 @ X64 @ X63 @ X62 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X62 ) ) )
      | ( zip_tseitin_2 @ X64 @ X65 @ X63 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X63 @ X62 @ X64 ) @ X65 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) @ X0 )
      | ( zip_tseitin_2 @ sk_D_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( zip_tseitin_3 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ( zip_tseitin_2 @ sk_D_1 @ X0 @ sk_A )
      | ( zip_tseitin_3 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','26','27','28'])).

thf('30',plain,
    ( ( zip_tseitin_3 @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( v1_funct_2 @ X57 @ X59 @ X58 )
      | ~ ( zip_tseitin_2 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('32',plain,
    ( ( zip_tseitin_3 @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
   <= ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('37',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['37','40','41'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['34','42'])).

thf('44',plain,(
    zip_tseitin_3 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60 = k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('50',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['33'])).

thf('51',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,
    ( ( r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_D_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','58'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D_1 )
      | ( k1_xboole_0 = sk_D_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('62',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,
    ( ( k1_xboole_0 = sk_D_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','63'])).

thf('65',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['37','40','41'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_xboole_0 = sk_D_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('68',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('69',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ ( sk_D @ X44 @ X42 ) @ X42 )
      | ( ( k1_relset_1 @ X42 @ X43 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('70',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D_1 )
      = sk_A )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D_1 )
        = sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('75',plain,
    ( ( k1_xboole_0 = sk_D_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('77',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76'])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['77','81'])).

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

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('83',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51
       != ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ~ ( zip_tseitin_1 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('84',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('85',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 )
      | ( X50 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('86',plain,(
    ! [X49: $i] :
      ( zip_tseitin_0 @ X49 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('87',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_0 @ X54 @ X55 )
      | ( zip_tseitin_1 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','90'])).

thf('92',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['66','92'])).

thf('94',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FJG6Nodt2n
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.72/2.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.72/2.92  % Solved by: fo/fo7.sh
% 2.72/2.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.72/2.92  % done 2417 iterations in 2.461s
% 2.72/2.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.72/2.92  % SZS output start Refutation
% 2.72/2.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.72/2.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.72/2.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.72/2.92  thf(sk_C_type, type, sk_C: $i).
% 2.72/2.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.72/2.92  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.72/2.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.72/2.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.72/2.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.72/2.92  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.72/2.92  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 2.72/2.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.72/2.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.72/2.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.72/2.92  thf(sk_A_type, type, sk_A: $i).
% 2.72/2.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.72/2.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.72/2.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.72/2.92  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 2.72/2.92  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 2.72/2.92  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.72/2.92  thf(sk_B_type, type, sk_B: $i).
% 2.72/2.92  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.72/2.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.72/2.92  thf(t9_funct_2, conjecture,
% 2.72/2.92    (![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.92     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.72/2.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.92       ( ( r1_tarski @ B @ C ) =>
% 2.72/2.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.72/2.92           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 2.72/2.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_0, negated_conjecture,
% 2.72/2.92    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.92        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.72/2.92            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.92          ( ( r1_tarski @ B @ C ) =>
% 2.72/2.92            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.72/2.92              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 2.72/2.92                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 2.72/2.92    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 2.72/2.92  thf('0', plain, ((r1_tarski @ sk_B @ sk_C)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(t118_zfmisc_1, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( r1_tarski @ A @ B ) =>
% 2.72/2.92       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 2.72/2.92         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 2.72/2.92  thf('1', plain,
% 2.72/2.92      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.72/2.92         (~ (r1_tarski @ X10 @ X11)
% 2.72/2.92          | (r1_tarski @ (k2_zfmisc_1 @ X12 @ X10) @ (k2_zfmisc_1 @ X12 @ X11)))),
% 2.72/2.92      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 2.72/2.92  thf('2', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_C))),
% 2.72/2.92      inference('sup-', [status(thm)], ['0', '1'])).
% 2.72/2.92  thf('3', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(t3_subset, axiom,
% 2.72/2.92    (![A:$i,B:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.72/2.92  thf('4', plain,
% 2.72/2.92      (![X16 : $i, X17 : $i]:
% 2.72/2.92         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.72/2.92      inference('cnf', [status(esa)], [t3_subset])).
% 2.72/2.92  thf('5', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 2.72/2.92      inference('sup-', [status(thm)], ['3', '4'])).
% 2.72/2.92  thf(t1_xboole_1, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.72/2.92       ( r1_tarski @ A @ C ) ))).
% 2.72/2.92  thf('6', plain,
% 2.72/2.92      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.72/2.92         (~ (r1_tarski @ X3 @ X4)
% 2.72/2.92          | ~ (r1_tarski @ X4 @ X5)
% 2.72/2.92          | (r1_tarski @ X3 @ X5))),
% 2.72/2.92      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.72/2.92  thf('7', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         ((r1_tarski @ sk_D_1 @ X0)
% 2.72/2.92          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 2.72/2.92      inference('sup-', [status(thm)], ['5', '6'])).
% 2.72/2.92  thf('8', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 2.72/2.92      inference('sup-', [status(thm)], ['2', '7'])).
% 2.72/2.92  thf('9', plain,
% 2.72/2.92      (![X16 : $i, X18 : $i]:
% 2.72/2.92         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 2.72/2.92      inference('cnf', [status(esa)], [t3_subset])).
% 2.72/2.92  thf('10', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['8', '9'])).
% 2.72/2.92  thf(cc2_relset_1, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.72/2.92  thf('11', plain,
% 2.72/2.92      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.72/2.92         ((v5_relat_1 @ X36 @ X38)
% 2.72/2.92          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 2.72/2.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.72/2.92  thf('12', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 2.72/2.92      inference('sup-', [status(thm)], ['10', '11'])).
% 2.72/2.92  thf(d19_relat_1, axiom,
% 2.72/2.92    (![A:$i,B:$i]:
% 2.72/2.92     ( ( v1_relat_1 @ B ) =>
% 2.72/2.92       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.72/2.92  thf('13', plain,
% 2.72/2.92      (![X24 : $i, X25 : $i]:
% 2.72/2.92         (~ (v5_relat_1 @ X24 @ X25)
% 2.72/2.92          | (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 2.72/2.92          | ~ (v1_relat_1 @ X24))),
% 2.72/2.92      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.72/2.92  thf('14', plain,
% 2.72/2.92      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C))),
% 2.72/2.92      inference('sup-', [status(thm)], ['12', '13'])).
% 2.72/2.92  thf('15', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(cc2_relat_1, axiom,
% 2.72/2.92    (![A:$i]:
% 2.72/2.92     ( ( v1_relat_1 @ A ) =>
% 2.72/2.92       ( ![B:$i]:
% 2.72/2.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.72/2.92  thf('16', plain,
% 2.72/2.92      (![X22 : $i, X23 : $i]:
% 2.72/2.92         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 2.72/2.92          | (v1_relat_1 @ X22)
% 2.72/2.92          | ~ (v1_relat_1 @ X23))),
% 2.72/2.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.72/2.92  thf('17', plain,
% 2.72/2.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['15', '16'])).
% 2.72/2.92  thf(fc6_relat_1, axiom,
% 2.72/2.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.72/2.92  thf('18', plain,
% 2.72/2.92      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 2.72/2.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.72/2.92  thf('19', plain, ((v1_relat_1 @ sk_D_1)),
% 2.72/2.92      inference('demod', [status(thm)], ['17', '18'])).
% 2.72/2.92  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 2.72/2.92      inference('demod', [status(thm)], ['14', '19'])).
% 2.72/2.92  thf('21', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(t8_funct_2, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.92     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.72/2.92         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.72/2.92       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 2.72/2.92         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 2.72/2.92             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 2.72/2.92           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_1, type, zip_tseitin_3 : $i > $i > $o).
% 2.72/2.92  thf(zf_stmt_2, axiom,
% 2.72/2.92    (![B:$i,A:$i]:
% 2.72/2.92     ( ( zip_tseitin_3 @ B @ A ) =>
% 2.72/2.92       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 2.72/2.92  thf(zf_stmt_4, axiom,
% 2.72/2.92    (![D:$i,C:$i,A:$i]:
% 2.72/2.92     ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 2.72/2.92       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 2.72/2.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_5, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.92     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.72/2.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.92       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 2.72/2.92         ( ( zip_tseitin_3 @ B @ A ) | ( zip_tseitin_2 @ D @ C @ A ) ) ) ))).
% 2.72/2.92  thf('22', plain,
% 2.72/2.92      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 2.72/2.92         ((zip_tseitin_3 @ X62 @ X63)
% 2.72/2.92          | ~ (v1_funct_1 @ X64)
% 2.72/2.92          | ~ (v1_funct_2 @ X64 @ X63 @ X62)
% 2.72/2.92          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X62)))
% 2.72/2.92          | (zip_tseitin_2 @ X64 @ X65 @ X63)
% 2.72/2.92          | ~ (r1_tarski @ (k2_relset_1 @ X63 @ X62 @ X64) @ X65))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.72/2.92  thf('23', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1) @ X0)
% 2.72/2.92          | (zip_tseitin_2 @ sk_D_1 @ X0 @ sk_A)
% 2.72/2.92          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)
% 2.72/2.92          | ~ (v1_funct_1 @ sk_D_1)
% 2.72/2.92          | (zip_tseitin_3 @ sk_B @ sk_A))),
% 2.72/2.92      inference('sup-', [status(thm)], ['21', '22'])).
% 2.72/2.92  thf('24', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf(redefinition_k2_relset_1, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.72/2.92  thf('25', plain,
% 2.72/2.92      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.72/2.92         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 2.72/2.92          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 2.72/2.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.72/2.92  thf('26', plain,
% 2.72/2.92      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['24', '25'])).
% 2.72/2.92  thf('27', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('28', plain, ((v1_funct_1 @ sk_D_1)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('29', plain,
% 2.72/2.92      (![X0 : $i]:
% 2.72/2.92         (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0)
% 2.72/2.92          | (zip_tseitin_2 @ sk_D_1 @ X0 @ sk_A)
% 2.72/2.92          | (zip_tseitin_3 @ sk_B @ sk_A))),
% 2.72/2.92      inference('demod', [status(thm)], ['23', '26', '27', '28'])).
% 2.72/2.92  thf('30', plain,
% 2.72/2.92      (((zip_tseitin_3 @ sk_B @ sk_A) | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 2.72/2.92      inference('sup-', [status(thm)], ['20', '29'])).
% 2.72/2.92  thf('31', plain,
% 2.72/2.92      (![X57 : $i, X58 : $i, X59 : $i]:
% 2.72/2.92         ((v1_funct_2 @ X57 @ X59 @ X58) | ~ (zip_tseitin_2 @ X57 @ X58 @ X59))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.72/2.92  thf('32', plain,
% 2.72/2.92      (((zip_tseitin_3 @ sk_B @ sk_A) | (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 2.72/2.92      inference('sup-', [status(thm)], ['30', '31'])).
% 2.72/2.92  thf('33', plain,
% 2.72/2.92      ((~ (v1_funct_1 @ sk_D_1)
% 2.72/2.92        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)
% 2.72/2.92        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('34', plain,
% 2.72/2.92      ((~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))
% 2.72/2.92         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)))),
% 2.72/2.92      inference('split', [status(esa)], ['33'])).
% 2.72/2.92  thf('35', plain, ((v1_funct_1 @ sk_D_1)),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('36', plain, ((~ (v1_funct_1 @ sk_D_1)) <= (~ ((v1_funct_1 @ sk_D_1)))),
% 2.72/2.92      inference('split', [status(esa)], ['33'])).
% 2.72/2.92  thf('37', plain, (((v1_funct_1 @ sk_D_1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['35', '36'])).
% 2.72/2.92  thf('38', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['8', '9'])).
% 2.72/2.92  thf('39', plain,
% 2.72/2.92      ((~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 2.72/2.92         <= (~
% 2.72/2.92             ((m1_subset_1 @ sk_D_1 @ 
% 2.72/2.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 2.72/2.92      inference('split', [status(esa)], ['33'])).
% 2.72/2.92  thf('40', plain,
% 2.72/2.92      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['38', '39'])).
% 2.72/2.92  thf('41', plain,
% 2.72/2.92      (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) | 
% 2.72/2.92       ~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 2.72/2.92       ~ ((v1_funct_1 @ sk_D_1))),
% 2.72/2.92      inference('split', [status(esa)], ['33'])).
% 2.72/2.92  thf('42', plain, (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 2.72/2.92      inference('sat_resolution*', [status(thm)], ['37', '40', '41'])).
% 2.72/2.92  thf('43', plain, (~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)),
% 2.72/2.92      inference('simpl_trail', [status(thm)], ['34', '42'])).
% 2.72/2.92  thf('44', plain, ((zip_tseitin_3 @ sk_B @ sk_A)),
% 2.72/2.92      inference('clc', [status(thm)], ['32', '43'])).
% 2.72/2.92  thf('45', plain,
% 2.72/2.92      (![X60 : $i, X61 : $i]:
% 2.72/2.92         (((X60) = (k1_xboole_0)) | ~ (zip_tseitin_3 @ X60 @ X61))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.72/2.92  thf('46', plain, (((sk_B) = (k1_xboole_0))),
% 2.72/2.92      inference('sup-', [status(thm)], ['44', '45'])).
% 2.72/2.92  thf('47', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('48', plain,
% 2.72/2.92      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 2.72/2.92      inference('split', [status(esa)], ['47'])).
% 2.72/2.92  thf('49', plain,
% 2.72/2.92      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('split', [status(esa)], ['47'])).
% 2.72/2.92  thf('50', plain,
% 2.72/2.92      ((~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))
% 2.72/2.92         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)))),
% 2.72/2.92      inference('split', [status(esa)], ['33'])).
% 2.72/2.92  thf('51', plain,
% 2.72/2.92      ((~ (v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C))
% 2.72/2.92         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) & 
% 2.72/2.92             (((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['49', '50'])).
% 2.72/2.92  thf('52', plain,
% 2.72/2.92      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('split', [status(esa)], ['47'])).
% 2.72/2.92  thf('53', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.92  thf('54', plain,
% 2.72/2.92      (((m1_subset_1 @ sk_D_1 @ 
% 2.72/2.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('sup+', [status(thm)], ['52', '53'])).
% 2.72/2.92  thf('55', plain,
% 2.72/2.92      (![X16 : $i, X17 : $i]:
% 2.72/2.92         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.72/2.92      inference('cnf', [status(esa)], [t3_subset])).
% 2.72/2.92  thf('56', plain,
% 2.72/2.92      (((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['54', '55'])).
% 2.72/2.92  thf(t113_zfmisc_1, axiom,
% 2.72/2.92    (![A:$i,B:$i]:
% 2.72/2.92     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.72/2.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.72/2.92  thf('57', plain,
% 2.72/2.92      (![X8 : $i, X9 : $i]:
% 2.72/2.92         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 2.72/2.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.72/2.92  thf('58', plain,
% 2.72/2.92      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['57'])).
% 2.72/2.92  thf('59', plain,
% 2.72/2.92      (((r1_tarski @ sk_D_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('demod', [status(thm)], ['56', '58'])).
% 2.72/2.92  thf(d10_xboole_0, axiom,
% 2.72/2.92    (![A:$i,B:$i]:
% 2.72/2.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.72/2.92  thf('60', plain,
% 2.72/2.92      (![X0 : $i, X2 : $i]:
% 2.72/2.92         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.72/2.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.72/2.92  thf('61', plain,
% 2.72/2.92      (((~ (r1_tarski @ k1_xboole_0 @ sk_D_1) | ((k1_xboole_0) = (sk_D_1))))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['59', '60'])).
% 2.72/2.92  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.72/2.92  thf('62', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 2.72/2.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.72/2.92  thf('63', plain,
% 2.72/2.92      ((((k1_xboole_0) = (sk_D_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('demod', [status(thm)], ['61', '62'])).
% 2.72/2.92  thf('64', plain,
% 2.72/2.92      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 2.72/2.92         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) & 
% 2.72/2.92             (((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('demod', [status(thm)], ['51', '63'])).
% 2.72/2.92  thf('65', plain, (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 2.72/2.92      inference('sat_resolution*', [status(thm)], ['37', '40', '41'])).
% 2.72/2.92  thf('66', plain,
% 2.72/2.92      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('simpl_trail', [status(thm)], ['64', '65'])).
% 2.72/2.92  thf('67', plain,
% 2.72/2.92      ((((k1_xboole_0) = (sk_D_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('demod', [status(thm)], ['61', '62'])).
% 2.72/2.92  thf('68', plain,
% 2.72/2.92      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.72/2.92      inference('sup-', [status(thm)], ['8', '9'])).
% 2.72/2.92  thf(t22_relset_1, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.72/2.92       ( ( ![D:$i]:
% 2.72/2.92           ( ~( ( r2_hidden @ D @ B ) & 
% 2.72/2.92                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 2.72/2.92         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 2.72/2.92  thf('69', plain,
% 2.72/2.92      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.72/2.92         ((r2_hidden @ (sk_D @ X44 @ X42) @ X42)
% 2.72/2.92          | ((k1_relset_1 @ X42 @ X43 @ X44) = (X42))
% 2.72/2.92          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 2.72/2.92      inference('cnf', [status(esa)], [t22_relset_1])).
% 2.72/2.92  thf('70', plain,
% 2.72/2.92      ((((k1_relset_1 @ sk_A @ sk_C @ sk_D_1) = (sk_A))
% 2.72/2.92        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_A) @ sk_A))),
% 2.72/2.92      inference('sup-', [status(thm)], ['68', '69'])).
% 2.72/2.92  thf('71', plain,
% 2.72/2.92      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_A) @ sk_A)
% 2.72/2.92         | ((k1_relset_1 @ sk_A @ sk_C @ sk_D_1) = (sk_A))))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('sup+', [status(thm)], ['67', '70'])).
% 2.72/2.92  thf('72', plain,
% 2.72/2.92      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('split', [status(esa)], ['47'])).
% 2.72/2.92  thf('73', plain,
% 2.72/2.92      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('split', [status(esa)], ['47'])).
% 2.72/2.92  thf('74', plain,
% 2.72/2.92      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('split', [status(esa)], ['47'])).
% 2.72/2.92  thf('75', plain,
% 2.72/2.92      ((((k1_xboole_0) = (sk_D_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('demod', [status(thm)], ['61', '62'])).
% 2.72/2.92  thf('76', plain,
% 2.72/2.92      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('split', [status(esa)], ['47'])).
% 2.72/2.92  thf('77', plain,
% 2.72/2.92      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 2.72/2.92         | ((k1_relset_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0) = (k1_xboole_0))))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('demod', [status(thm)], ['71', '72', '73', '74', '75', '76'])).
% 2.72/2.92  thf('78', plain,
% 2.72/2.92      (![X8 : $i, X9 : $i]:
% 2.72/2.92         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 2.72/2.92      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.72/2.92  thf('79', plain,
% 2.72/2.92      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 2.72/2.92      inference('simplify', [status(thm)], ['78'])).
% 2.72/2.92  thf(t152_zfmisc_1, axiom,
% 2.72/2.92    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.72/2.92  thf('80', plain,
% 2.72/2.92      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 2.72/2.92      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.72/2.92  thf('81', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.72/2.92      inference('sup-', [status(thm)], ['79', '80'])).
% 2.72/2.92  thf('82', plain,
% 2.72/2.92      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0) = (k1_xboole_0)))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('clc', [status(thm)], ['77', '81'])).
% 2.72/2.92  thf(d1_funct_2, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.72/2.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.72/2.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.72/2.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.72/2.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.72/2.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.72/2.92  thf(zf_stmt_6, axiom,
% 2.72/2.92    (![C:$i,B:$i,A:$i]:
% 2.72/2.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.72/2.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.72/2.92  thf('83', plain,
% 2.72/2.92      (![X51 : $i, X52 : $i, X53 : $i]:
% 2.72/2.92         (((X51) != (k1_relset_1 @ X51 @ X52 @ X53))
% 2.72/2.92          | (v1_funct_2 @ X53 @ X51 @ X52)
% 2.72/2.92          | ~ (zip_tseitin_1 @ X53 @ X52 @ X51))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_6])).
% 2.72/2.92  thf('84', plain,
% 2.72/2.92      (((((k1_xboole_0) != (k1_xboole_0))
% 2.72/2.92         | ~ (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0)
% 2.72/2.92         | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C)))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('sup-', [status(thm)], ['82', '83'])).
% 2.72/2.92  thf(zf_stmt_7, axiom,
% 2.72/2.92    (![B:$i,A:$i]:
% 2.72/2.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.72/2.92       ( zip_tseitin_0 @ B @ A ) ))).
% 2.72/2.92  thf('85', plain,
% 2.72/2.92      (![X49 : $i, X50 : $i]:
% 2.72/2.92         ((zip_tseitin_0 @ X49 @ X50) | ((X50) != (k1_xboole_0)))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_7])).
% 2.72/2.92  thf('86', plain, (![X49 : $i]: (zip_tseitin_0 @ X49 @ k1_xboole_0)),
% 2.72/2.92      inference('simplify', [status(thm)], ['85'])).
% 2.72/2.92  thf(t4_subset_1, axiom,
% 2.72/2.92    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.72/2.92  thf('87', plain,
% 2.72/2.92      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 2.72/2.92      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.72/2.92  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.72/2.92  thf(zf_stmt_9, type, zip_tseitin_0 : $i > $i > $o).
% 2.72/2.92  thf(zf_stmt_10, axiom,
% 2.72/2.92    (![A:$i,B:$i,C:$i]:
% 2.72/2.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.72/2.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.72/2.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.72/2.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.72/2.92  thf('88', plain,
% 2.72/2.92      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.72/2.92         (~ (zip_tseitin_0 @ X54 @ X55)
% 2.72/2.92          | (zip_tseitin_1 @ X56 @ X54 @ X55)
% 2.72/2.92          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 2.72/2.92      inference('cnf', [status(esa)], [zf_stmt_10])).
% 2.72/2.92  thf('89', plain,
% 2.72/2.92      (![X0 : $i, X1 : $i]:
% 2.72/2.92         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.72/2.92      inference('sup-', [status(thm)], ['87', '88'])).
% 2.72/2.92  thf('90', plain,
% 2.72/2.92      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.72/2.92      inference('sup-', [status(thm)], ['86', '89'])).
% 2.72/2.92  thf('91', plain,
% 2.72/2.92      (((((k1_xboole_0) != (k1_xboole_0))
% 2.72/2.92         | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C)))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('demod', [status(thm)], ['84', '90'])).
% 2.72/2.92  thf('92', plain,
% 2.72/2.92      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 2.72/2.92         <= ((((sk_A) = (k1_xboole_0))))),
% 2.72/2.92      inference('simplify', [status(thm)], ['91'])).
% 2.72/2.92  thf('93', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 2.72/2.92      inference('demod', [status(thm)], ['66', '92'])).
% 2.72/2.92  thf('94', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 2.72/2.92      inference('split', [status(esa)], ['47'])).
% 2.72/2.92  thf('95', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 2.72/2.92      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 2.72/2.92  thf('96', plain, (((sk_B) != (k1_xboole_0))),
% 2.72/2.92      inference('simpl_trail', [status(thm)], ['48', '95'])).
% 2.72/2.92  thf('97', plain, ($false),
% 2.72/2.92      inference('simplify_reflect-', [status(thm)], ['46', '96'])).
% 2.72/2.92  
% 2.72/2.92  % SZS output end Refutation
% 2.72/2.92  
% 2.72/2.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
