%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0WpHStUEZO

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:36 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 142 expanded)
%              Number of leaves         :   47 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  823 (1431 expanded)
%              Number of equality atoms :   80 ( 122 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X34 )
       != X32 )
      | ~ ( r2_hidden @ X35 @ X32 )
      | ( r2_hidden @ ( k4_tarski @ X35 @ ( sk_E @ X35 @ X34 ) ) @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) @ sk_C ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X14
        = ( k2_tarski @ X12 @ X13 ) )
      | ( X14
        = ( k1_tarski @ X13 ) )
      | ( X14
        = ( k1_tarski @ X12 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != ( k1_tarski @ X19 ) )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['46','51'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('53',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('58',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['23','57','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0WpHStUEZO
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:32 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 311 iterations in 0.226s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.52/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.72  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.52/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.52/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(d1_xboole_0, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.72  thf(t62_funct_2, conjecture,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.52/0.72         ( m1_subset_1 @
% 0.52/0.72           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.52/0.72       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.52/0.72         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.52/0.72           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.52/0.72            ( m1_subset_1 @
% 0.52/0.72              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.52/0.72          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.52/0.72            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.52/0.72              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_C @ 
% 0.52/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(t22_relset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.52/0.72       ( ( ![D:$i]:
% 0.52/0.72           ( ~( ( r2_hidden @ D @ B ) & 
% 0.52/0.72                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.52/0.72         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.72         (((k1_relset_1 @ X32 @ X33 @ X34) != (X32))
% 0.52/0.72          | ~ (r2_hidden @ X35 @ X32)
% 0.52/0.72          | (r2_hidden @ (k4_tarski @ X35 @ (sk_E @ X35 @ X34)) @ X34)
% 0.52/0.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.52/0.72      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.52/0.72          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.52/0.72          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.52/0.72              != (k1_tarski @ sk_A)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.72  thf('4', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(d1_funct_2, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.52/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.52/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_1, axiom,
% 0.52/0.72    (![C:$i,B:$i,A:$i]:
% 0.52/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.52/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.52/0.72         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.52/0.72          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 0.52/0.72          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.52/0.72        | ((k1_tarski @ sk_A)
% 0.52/0.72            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.72  thf(zf_stmt_2, axiom,
% 0.52/0.73    (![B:$i,A:$i]:
% 0.52/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (![X37 : $i, X38 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_5, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.52/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.52/0.73         (~ (zip_tseitin_0 @ X42 @ X43)
% 0.52/0.73          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 0.52/0.73          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.52/0.73        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      ((((sk_B_1) = (k1_xboole_0))
% 0.52/0.73        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['7', '10'])).
% 0.52/0.73  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('13', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.52/0.73      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['6', '13'])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.52/0.73          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.52/0.73          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['3', '14'])).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.52/0.73          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['15'])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.52/0.73        | (r2_hidden @ 
% 0.52/0.73           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.73            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)) @ 
% 0.52/0.73           sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['0', '16'])).
% 0.52/0.73  thf(t69_enumset1, axiom,
% 0.52/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.52/0.73  thf('18', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.52/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.73  thf(fc3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X10 @ X11))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.52/0.73  thf('20', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      ((r2_hidden @ 
% 0.52/0.73        (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.73         (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)) @ 
% 0.52/0.73        sk_C)),
% 0.52/0.73      inference('clc', [status(thm)], ['17', '20'])).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.73  thf('23', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.52/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.73         ((v4_relat_1 @ X26 @ X27)
% 0.52/0.73          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.73  thf('26', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.73  thf(d18_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ B ) =>
% 0.52/0.73       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      (![X16 : $i, X17 : $i]:
% 0.52/0.73         (~ (v4_relat_1 @ X16 @ X17)
% 0.52/0.73          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.52/0.73          | ~ (v1_relat_1 @ X16))),
% 0.52/0.73      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.73        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc1_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( v1_relat_1 @ C ) ))).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.52/0.73         ((v1_relat_1 @ X23)
% 0.52/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.73  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.73  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['28', '31'])).
% 0.52/0.73  thf('33', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.52/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.73  thf(l45_zfmisc_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.52/0.73       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.52/0.73            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.73         (((X14) = (k2_tarski @ X12 @ X13))
% 0.52/0.73          | ((X14) = (k1_tarski @ X13))
% 0.52/0.73          | ((X14) = (k1_tarski @ X12))
% 0.52/0.73          | ((X14) = (k1_xboole_0))
% 0.52/0.73          | ~ (r1_tarski @ X14 @ (k2_tarski @ X12 @ X13)))),
% 0.52/0.73      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.52/0.73          | ((X1) = (k1_xboole_0))
% 0.52/0.73          | ((X1) = (k1_tarski @ X0))
% 0.52/0.73          | ((X1) = (k1_tarski @ X0))
% 0.52/0.73          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('36', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         (((X1) = (k2_tarski @ X0 @ X0))
% 0.52/0.73          | ((X1) = (k1_tarski @ X0))
% 0.52/0.73          | ((X1) = (k1_xboole_0))
% 0.52/0.73          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['35'])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['32', '36'])).
% 0.52/0.73  thf('38', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.52/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['37', '38'])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['39'])).
% 0.52/0.73  thf(t14_funct_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.73       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.52/0.73         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      (![X19 : $i, X20 : $i]:
% 0.52/0.73         (((k1_relat_1 @ X20) != (k1_tarski @ X19))
% 0.52/0.73          | ((k2_relat_1 @ X20) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 0.52/0.73          | ~ (v1_funct_1 @ X20)
% 0.52/0.73          | ~ (v1_relat_1 @ X20))),
% 0.52/0.73      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.52/0.73          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.52/0.73          | ~ (v1_relat_1 @ X0)
% 0.52/0.73          | ~ (v1_funct_1 @ X0)
% 0.52/0.73          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.52/0.73        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.73        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.52/0.73      inference('eq_res', [status(thm)], ['42'])).
% 0.52/0.73  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.73  thf('46', plain,
% 0.52/0.73      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.52/0.73        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.52/0.73  thf('47', plain,
% 0.52/0.73      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.52/0.73         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ 
% 0.52/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.73  thf('49', plain,
% 0.52/0.73      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.73         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.52/0.73          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.73  thf('50', plain,
% 0.52/0.73      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.52/0.73         = (k2_relat_1 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.73  thf('51', plain,
% 0.52/0.73      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.52/0.73      inference('demod', [status(thm)], ['47', '50'])).
% 0.52/0.73  thf('52', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify_reflect-', [status(thm)], ['46', '51'])).
% 0.52/0.73  thf(t64_relat_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ A ) =>
% 0.52/0.73       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.73           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.73         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.73  thf('53', plain,
% 0.52/0.73      (![X18 : $i]:
% 0.52/0.73         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 0.52/0.73          | ((X18) = (k1_xboole_0))
% 0.52/0.73          | ~ (v1_relat_1 @ X18))),
% 0.52/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.52/0.73  thf('54', plain,
% 0.52/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.73        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.73        | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.52/0.73  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.73  thf('56', plain,
% 0.52/0.73      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['54', '55'])).
% 0.52/0.73  thf('57', plain, (((sk_C) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['56'])).
% 0.52/0.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.73  thf('58', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.52/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.73  thf('59', plain,
% 0.52/0.73      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.52/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.73  thf(t7_ordinal1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.73  thf('60', plain,
% 0.52/0.73      (![X21 : $i, X22 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.52/0.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.52/0.73  thf('61', plain,
% 0.52/0.73      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['59', '60'])).
% 0.52/0.73  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.73      inference('sup-', [status(thm)], ['58', '61'])).
% 0.52/0.73  thf('63', plain, ($false),
% 0.52/0.73      inference('demod', [status(thm)], ['23', '57', '62'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
