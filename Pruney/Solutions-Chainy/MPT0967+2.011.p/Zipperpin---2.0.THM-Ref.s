%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vf2KE9NG50

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:12 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  255 (4239 expanded)
%              Number of leaves         :   44 (1321 expanded)
%              Depth                    :   32
%              Number of atoms          : 1685 (34949 expanded)
%              Number of equality atoms :  153 (2839 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X13 ) @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','17','18'])).

thf('20',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('32',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X17 ) @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('40',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('41',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('55',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('63',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_B )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('82',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','82'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','85'])).

thf('87',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('88',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('90',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('91',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('93',plain,(
    ! [X35: $i] :
      ( zip_tseitin_0 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('95',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('96',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','93','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('98',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('99',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('100',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('101',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['98','101'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('103',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v5_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('106',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('107',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('112',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( v5_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','108'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','118'])).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v5_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','108'])).

thf('125',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['112','113'])).

thf('126',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','96','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('133',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','135'])).

thf('137',plain,(
    ! [X35: $i] :
      ( zip_tseitin_0 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('138',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('139',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','96','130'])).

thf('143',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','141','142'])).

thf('144',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('145',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('146',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('147',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','148'])).

thf('150',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('151',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('152',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('153',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('154',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['150','155'])).

thf('157',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('158',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('159',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','149','156','157','158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['68','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['61','160'])).

thf('162',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('163',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['161','164'])).

thf('166',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['33','165'])).

thf('167',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','166'])).

thf('168',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['23','167'])).

thf('169',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('170',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('173',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('174',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('176',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('182',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('183',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['177','186'])).

thf('188',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X11 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['63'])).

thf('194',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','149','156','157','158'])).

thf('195',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['192','195'])).

thf('197',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['68','159'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('206',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['174','206'])).

thf('208',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['171','207'])).

thf('209',plain,(
    $false ),
    inference(demod,[status(thm)],['20','208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vf2KE9NG50
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 764 iterations in 0.504s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.94  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.94  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.75/0.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.75/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.75/0.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.94  thf(t9_funct_2, conjecture,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.94       ( ( r1_tarski @ B @ C ) =>
% 0.75/0.94         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.75/0.94           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.75/0.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.94            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.94          ( ( r1_tarski @ B @ C ) =>
% 0.75/0.94            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.75/0.94              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.75/0.94                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.75/0.94  thf('0', plain,
% 0.75/0.94      ((~ (v1_funct_1 @ sk_D)
% 0.75/0.94        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.75/0.94        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.75/0.94         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.75/0.94      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.94  thf('5', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t118_zfmisc_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( r1_tarski @ A @ B ) =>
% 0.75/0.94       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.75/0.94         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X13 @ X14)
% 0.75/0.94          | (r1_tarski @ (k2_zfmisc_1 @ X15 @ X13) @ (k2_zfmisc_1 @ X15 @ X14)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_C_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['5', '6'])).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t3_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (![X18 : $i, X19 : $i]:
% 0.75/0.94         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.94  thf('10', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.94  thf(t1_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.75/0.94       ( r1_tarski @ A @ C ) ))).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X7 @ X8)
% 0.75/0.94          | ~ (r1_tarski @ X8 @ X9)
% 0.75/0.94          | (r1_tarski @ X7 @ X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r1_tarski @ sk_D @ X0)
% 0.75/0.94          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('13', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['7', '12'])).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      (![X18 : $i, X20 : $i]:
% 0.75/0.94         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.75/0.94         <= (~
% 0.75/0.94             ((m1_subset_1 @ sk_D @ 
% 0.75/0.94               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['15', '16'])).
% 0.75/0.94  thf('18', plain,
% 0.75/0.94      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 0.75/0.94       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.75/0.94       ~ ((v1_funct_1 @ sk_D))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('19', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.75/0.94      inference('sat_resolution*', [status(thm)], ['4', '17', '18'])).
% 0.75/0.94  thf('20', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.75/0.94      inference('simpl_trail', [status(thm)], ['1', '19'])).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.94  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.75/0.94         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.75/0.94          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.75/0.94      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.94  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(d1_funct_2, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.94           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.94             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.94         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.94           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.94             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_1, axiom,
% 0.75/0.94    (![C:$i,B:$i,A:$i]:
% 0.75/0.94     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.94       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.94  thf('25', plain,
% 0.75/0.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.75/0.94         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.75/0.94          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.75/0.94          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('26', plain,
% 0.75/0.94      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.75/0.94        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.94  thf('27', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.75/0.94         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.75/0.94          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.94  thf('29', plain,
% 0.75/0.94      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.75/0.94      inference('sup-', [status(thm)], ['27', '28'])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.75/0.94      inference('demod', [status(thm)], ['26', '29'])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.94  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/0.94  thf(zf_stmt_4, axiom,
% 0.75/0.94    (![B:$i,A:$i]:
% 0.75/0.94     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.94       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.94  thf(zf_stmt_5, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/0.94         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.94           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.94             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.75/0.94         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.75/0.94          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['31', '32'])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (![X35 : $i, X36 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.94  thf(t113_zfmisc_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.75/0.94       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.75/0.94          | ((X12) != (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['35'])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.75/0.94      inference('sup+', [status(thm)], ['34', '36'])).
% 0.75/0.94  thf(d3_tarski, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_tarski @ A @ B ) <=>
% 0.75/0.94       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X1 : $i, X3 : $i]:
% 0.75/0.94         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.94  thf(dt_k2_subset_1, axiom,
% 0.75/0.94    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (![X17 : $i]: (m1_subset_1 @ (k2_subset_1 @ X17) @ (k1_zfmisc_1 @ X17))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.75/0.94  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.75/0.94  thf('40', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.75/0.94      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.75/0.94  thf('41', plain, (![X17 : $i]: (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X17))),
% 0.75/0.94      inference('demod', [status(thm)], ['39', '40'])).
% 0.75/0.94  thf(t5_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.75/0.94          ( v1_xboole_0 @ C ) ) ))).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X21 @ X22)
% 0.75/0.94          | ~ (v1_xboole_0 @ X23)
% 0.75/0.94          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t5_subset])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['41', '42'])).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '43'])).
% 0.75/0.94  thf('45', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.94  thf(d10_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (![X4 : $i, X6 : $i]:
% 0.75/0.94         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D)
% 0.75/0.94        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.94  thf('48', plain,
% 0.75/0.94      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.75/0.94        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['44', '47'])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.94          | (zip_tseitin_0 @ sk_B @ X0)
% 0.75/0.94          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['37', '48'])).
% 0.75/0.94  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.75/0.94  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 0.75/0.94      inference('demod', [status(thm)], ['49', '50'])).
% 0.75/0.94  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '43'])).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '43'])).
% 0.75/0.94  thf('55', plain,
% 0.75/0.94      (![X4 : $i, X6 : $i]:
% 0.75/0.94         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('56', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['54', '55'])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['53', '56'])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['52', '57'])).
% 0.75/0.94  thf('59', plain,
% 0.75/0.94      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['35'])).
% 0.75/0.94  thf('60', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('61', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (((sk_D) = (k1_xboole_0))
% 0.75/0.94          | (zip_tseitin_0 @ sk_B @ X0)
% 0.75/0.94          | ~ (v1_xboole_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['51', '60'])).
% 0.75/0.94  thf('62', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['53', '56'])).
% 0.75/0.94  thf('63', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('64', plain,
% 0.75/0.94      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('65', plain,
% 0.75/0.94      ((![X0 : $i]:
% 0.75/0.94          (((X0) != (k1_xboole_0))
% 0.75/0.94           | ~ (v1_xboole_0 @ sk_B)
% 0.75/0.94           | ~ (v1_xboole_0 @ X0)))
% 0.75/0.94         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['62', '64'])).
% 0.75/0.94  thf('66', plain,
% 0.75/0.94      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B)))
% 0.75/0.94         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['65'])).
% 0.75/0.94  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('68', plain,
% 0.75/0.94      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.75/0.94      inference('simplify_reflect+', [status(thm)], ['66', '67'])).
% 0.75/0.94  thf('69', plain,
% 0.75/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('71', plain,
% 0.75/0.94      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['69', '70'])).
% 0.75/0.94  thf('72', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '43'])).
% 0.75/0.94  thf('73', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.75/0.94          | ((X11) != (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.94  thf('74', plain,
% 0.75/0.94      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['73'])).
% 0.75/0.94  thf('75', plain,
% 0.75/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('76', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('77', plain,
% 0.75/0.94      (((m1_subset_1 @ sk_D @ 
% 0.75/0.94         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['75', '76'])).
% 0.75/0.94  thf('78', plain,
% 0.75/0.94      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['74', '77'])).
% 0.75/0.94  thf('79', plain,
% 0.75/0.94      (![X18 : $i, X19 : $i]:
% 0.75/0.94         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.94  thf('80', plain,
% 0.75/0.94      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('81', plain,
% 0.75/0.94      (![X4 : $i, X6 : $i]:
% 0.75/0.94         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('82', plain,
% 0.75/0.94      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['80', '81'])).
% 0.75/0.94  thf('83', plain,
% 0.75/0.94      (((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_D))))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['72', '82'])).
% 0.75/0.94  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('85', plain,
% 0.75/0.94      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['83', '84'])).
% 0.75/0.94  thf('86', plain,
% 0.75/0.94      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['71', '85'])).
% 0.75/0.94  thf('87', plain,
% 0.75/0.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.75/0.94         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.75/0.94          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.75/0.94          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('88', plain,
% 0.75/0.94      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 0.75/0.94         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['86', '87'])).
% 0.75/0.94  thf('89', plain,
% 0.75/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('90', plain,
% 0.75/0.94      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['31', '32'])).
% 0.75/0.94  thf('91', plain,
% 0.75/0.94      (((~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)
% 0.75/0.94         | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['89', '90'])).
% 0.75/0.94  thf('92', plain,
% 0.75/0.94      (![X35 : $i, X36 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.94  thf('93', plain, (![X35 : $i]: (zip_tseitin_0 @ X35 @ k1_xboole_0)),
% 0.75/0.94      inference('simplify', [status(thm)], ['92'])).
% 0.75/0.94  thf('94', plain,
% 0.75/0.94      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['83', '84'])).
% 0.75/0.94  thf('95', plain,
% 0.75/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('96', plain,
% 0.75/0.94      (((zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['91', '93', '94', '95'])).
% 0.75/0.94  thf('97', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '43'])).
% 0.75/0.94  thf('98', plain, (![X17 : $i]: (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X17))),
% 0.75/0.94      inference('demod', [status(thm)], ['39', '40'])).
% 0.75/0.94  thf('99', plain,
% 0.75/0.94      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['35'])).
% 0.75/0.94  thf(cc2_relset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.75/0.94  thf('100', plain,
% 0.75/0.94      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.94         ((v5_relat_1 @ X29 @ X31)
% 0.75/0.94          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.94  thf('101', plain,
% 0.75/0.94      (![X1 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.75/0.94          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['99', '100'])).
% 0.75/0.94  thf('102', plain, ((v5_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['98', '101'])).
% 0.75/0.94  thf(d19_relat_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( v1_relat_1 @ B ) =>
% 0.75/0.94       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.94  thf('103', plain,
% 0.75/0.94      (![X24 : $i, X25 : $i]:
% 0.75/0.94         (~ (v5_relat_1 @ X24 @ X25)
% 0.75/0.94          | (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.75/0.94          | ~ (v1_relat_1 @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.75/0.94  thf('104', plain,
% 0.75/0.94      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.94        | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['102', '103'])).
% 0.75/0.94  thf('105', plain, (![X17 : $i]: (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X17))),
% 0.75/0.94      inference('demod', [status(thm)], ['39', '40'])).
% 0.75/0.94  thf('106', plain,
% 0.75/0.94      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['35'])).
% 0.75/0.94  thf(cc1_relset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.94       ( v1_relat_1 @ C ) ))).
% 0.75/0.94  thf('107', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.94         ((v1_relat_1 @ X26)
% 0.75/0.94          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.75/0.94      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.94  thf('108', plain,
% 0.75/0.94      (![X1 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.75/0.94          | (v1_relat_1 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['106', '107'])).
% 0.75/0.94  thf('109', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['105', '108'])).
% 0.75/0.94  thf('110', plain, ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.75/0.94      inference('demod', [status(thm)], ['104', '109'])).
% 0.75/0.94  thf('111', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['54', '55'])).
% 0.75/0.94  thf('112', plain,
% 0.75/0.94      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.94        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['110', '111'])).
% 0.75/0.94  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('114', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['112', '113'])).
% 0.75/0.94  thf('115', plain,
% 0.75/0.94      (![X24 : $i, X25 : $i]:
% 0.75/0.94         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.75/0.94          | (v5_relat_1 @ X24 @ X25)
% 0.75/0.94          | ~ (v1_relat_1 @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.75/0.94  thf('116', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.75/0.94          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.94          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['114', '115'])).
% 0.75/0.94  thf('117', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['105', '108'])).
% 0.75/0.94  thf('118', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (r1_tarski @ k1_xboole_0 @ X0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['116', '117'])).
% 0.75/0.94  thf('119', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['97', '118'])).
% 0.75/0.94  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('121', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.75/0.94      inference('demod', [status(thm)], ['119', '120'])).
% 0.75/0.94  thf('122', plain,
% 0.75/0.94      (![X24 : $i, X25 : $i]:
% 0.75/0.94         (~ (v5_relat_1 @ X24 @ X25)
% 0.75/0.94          | (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.75/0.94          | ~ (v1_relat_1 @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.75/0.94  thf('123', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_relat_1 @ k1_xboole_0)
% 0.75/0.94          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['121', '122'])).
% 0.75/0.94  thf('124', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['105', '108'])).
% 0.75/0.94  thf('125', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['112', '113'])).
% 0.75/0.94  thf('126', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.75/0.94      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.75/0.94  thf('127', plain,
% 0.75/0.94      (![X18 : $i, X20 : $i]:
% 0.75/0.94         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.94  thf('128', plain,
% 0.75/0.94      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['126', '127'])).
% 0.75/0.94  thf('129', plain,
% 0.75/0.94      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.75/0.94         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.75/0.94          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.94  thf('130', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['128', '129'])).
% 0.75/0.94  thf('131', plain,
% 0.75/0.94      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['88', '96', '130'])).
% 0.75/0.94  thf('132', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['128', '129'])).
% 0.75/0.94  thf('133', plain,
% 0.75/0.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.75/0.94         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.75/0.94          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.75/0.94          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('134', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 0.75/0.94          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.75/0.94          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['132', '133'])).
% 0.75/0.94  thf('135', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.75/0.94          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['134'])).
% 0.75/0.94  thf('136', plain,
% 0.75/0.94      ((![X0 : $i]:
% 0.75/0.94          (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.75/0.94           | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['131', '135'])).
% 0.75/0.94  thf('137', plain, (![X35 : $i]: (zip_tseitin_0 @ X35 @ k1_xboole_0)),
% 0.75/0.94      inference('simplify', [status(thm)], ['92'])).
% 0.75/0.94  thf('138', plain,
% 0.75/0.94      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['126', '127'])).
% 0.75/0.94  thf('139', plain,
% 0.75/0.94      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.75/0.94         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.75/0.94          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.94  thf('140', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['138', '139'])).
% 0.75/0.94  thf('141', plain,
% 0.75/0.94      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['137', '140'])).
% 0.75/0.94  thf('142', plain,
% 0.75/0.94      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['88', '96', '130'])).
% 0.75/0.94  thf('143', plain,
% 0.75/0.94      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['136', '141', '142'])).
% 0.75/0.94  thf('144', plain,
% 0.75/0.94      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('demod', [status(thm)], ['83', '84'])).
% 0.75/0.94  thf('145', plain,
% 0.75/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('146', plain,
% 0.75/0.94      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.75/0.94         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('147', plain,
% 0.75/0.94      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.75/0.94         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.75/0.94             (((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['145', '146'])).
% 0.75/0.94  thf('148', plain,
% 0.75/0.94      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 0.75/0.94         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.75/0.94             (((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['144', '147'])).
% 0.75/0.94  thf('149', plain,
% 0.75/0.94      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['143', '148'])).
% 0.75/0.94  thf('150', plain,
% 0.75/0.94      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.75/0.94         <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['74', '77'])).
% 0.75/0.94  thf('151', plain,
% 0.75/0.94      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['73'])).
% 0.75/0.94  thf('152', plain,
% 0.75/0.94      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('153', plain,
% 0.75/0.94      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.75/0.94         <= (~
% 0.75/0.94             ((m1_subset_1 @ sk_D @ 
% 0.75/0.94               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('154', plain,
% 0.75/0.94      ((~ (m1_subset_1 @ sk_D @ 
% 0.75/0.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.75/0.94         <= (~
% 0.75/0.94             ((m1_subset_1 @ sk_D @ 
% 0.75/0.94               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.75/0.94             (((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['152', '153'])).
% 0.75/0.94  thf('155', plain,
% 0.75/0.94      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.75/0.94         <= (~
% 0.75/0.94             ((m1_subset_1 @ sk_D @ 
% 0.75/0.94               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.75/0.94             (((sk_A) = (k1_xboole_0))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['151', '154'])).
% 0.75/0.94  thf('156', plain,
% 0.75/0.94      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.75/0.94       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['150', '155'])).
% 0.75/0.94  thf('157', plain,
% 0.75/0.94      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.75/0.94       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('158', plain,
% 0.75/0.94      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('159', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.75/0.94      inference('sat_resolution*', [status(thm)],
% 0.75/0.94                ['4', '149', '156', '157', '158'])).
% 0.75/0.94  thf('160', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.75/0.94      inference('simpl_trail', [status(thm)], ['68', '159'])).
% 0.75/0.94  thf('161', plain,
% 0.75/0.94      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.75/0.94      inference('clc', [status(thm)], ['61', '160'])).
% 0.75/0.94  thf('162', plain,
% 0.75/0.94      (![X35 : $i, X36 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.94  thf('163', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('164', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['162', '163'])).
% 0.75/0.94  thf('165', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.75/0.94      inference('clc', [status(thm)], ['161', '164'])).
% 0.75/0.94  thf('166', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.75/0.94      inference('demod', [status(thm)], ['33', '165'])).
% 0.75/0.94  thf('167', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.75/0.94      inference('demod', [status(thm)], ['30', '166'])).
% 0.75/0.94  thf('168', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['23', '167'])).
% 0.75/0.94  thf('169', plain,
% 0.75/0.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.75/0.94         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.75/0.94          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.75/0.94          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('170', plain,
% 0.75/0.94      ((((sk_A) != (sk_A))
% 0.75/0.94        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.75/0.94        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['168', '169'])).
% 0.75/0.94  thf('171', plain,
% 0.75/0.94      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.75/0.94        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 0.75/0.94      inference('simplify', [status(thm)], ['170'])).
% 0.75/0.94  thf('172', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.94  thf('173', plain,
% 0.75/0.94      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.75/0.94         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.75/0.94          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.75/0.94          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.94  thf('174', plain,
% 0.75/0.94      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.75/0.94        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['172', '173'])).
% 0.75/0.94  thf('175', plain,
% 0.75/0.94      (![X35 : $i, X36 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.75/0.94  thf('176', plain,
% 0.75/0.94      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.75/0.94      inference('simplify', [status(thm)], ['73'])).
% 0.75/0.94  thf('177', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.75/0.94      inference('sup+', [status(thm)], ['175', '176'])).
% 0.75/0.94  thf('178', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('179', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X13 @ X14)
% 0.75/0.94          | (r1_tarski @ (k2_zfmisc_1 @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.75/0.94  thf('180', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (r1_tarski @ (k2_zfmisc_1 @ sk_B @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['178', '179'])).
% 0.75/0.94  thf('181', plain,
% 0.75/0.94      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['52', '57'])).
% 0.75/0.94  thf('182', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.75/0.94      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.75/0.94  thf('183', plain,
% 0.75/0.94      (![X4 : $i, X6 : $i]:
% 0.75/0.94         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('184', plain,
% 0.75/0.94      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['182', '183'])).
% 0.75/0.94  thf('185', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X1 @ X0)
% 0.75/0.94          | ~ (v1_xboole_0 @ X0)
% 0.75/0.94          | ((X1) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['181', '184'])).
% 0.75/0.94  thf('186', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.75/0.94          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['180', '185'])).
% 0.75/0.94  thf('187', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.94          | (zip_tseitin_0 @ sk_C_1 @ X1)
% 0.75/0.94          | ((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['177', '186'])).
% 0.75/0.94  thf('188', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('189', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ sk_C_1 @ X1)
% 0.75/0.94          | ((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['187', '188'])).
% 0.75/0.94  thf('190', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i]:
% 0.75/0.94         (((X10) = (k1_xboole_0))
% 0.75/0.94          | ((X11) = (k1_xboole_0))
% 0.75/0.94          | ((k2_zfmisc_1 @ X11 @ X10) != (k1_xboole_0)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.94  thf('191', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.94          | (zip_tseitin_0 @ sk_C_1 @ X1)
% 0.75/0.94          | ((sk_B) = (k1_xboole_0))
% 0.75/0.94          | ((X0) = (k1_xboole_0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['189', '190'])).
% 0.75/0.94  thf('192', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((X0) = (k1_xboole_0))
% 0.75/0.94          | ((sk_B) = (k1_xboole_0))
% 0.75/0.94          | (zip_tseitin_0 @ sk_C_1 @ X1))),
% 0.75/0.94      inference('simplify', [status(thm)], ['191'])).
% 0.75/0.94  thf('193', plain,
% 0.75/0.94      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.75/0.94      inference('split', [status(esa)], ['63'])).
% 0.75/0.94  thf('194', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.75/0.94      inference('sat_resolution*', [status(thm)],
% 0.75/0.94                ['4', '149', '156', '157', '158'])).
% 0.75/0.94  thf('195', plain, (((sk_B) != (k1_xboole_0))),
% 0.75/0.94      inference('simpl_trail', [status(thm)], ['193', '194'])).
% 0.75/0.94  thf('196', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((X0) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C_1 @ X1))),
% 0.75/0.94      inference('simplify_reflect-', [status(thm)], ['192', '195'])).
% 0.75/0.94  thf('197', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.75/0.94  thf('198', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ sk_C_1 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['196', '197'])).
% 0.75/0.94  thf('199', plain,
% 0.75/0.94      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.75/0.94        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['44', '47'])).
% 0.75/0.94  thf('200', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ sk_C_1 @ X0)
% 0.75/0.94          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_D)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['198', '199'])).
% 0.75/0.94  thf('201', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('202', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (((sk_D) = (k1_xboole_0))
% 0.75/0.94          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 0.75/0.94          | ~ (v1_xboole_0 @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['200', '201'])).
% 0.75/0.94  thf('203', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.75/0.94      inference('simpl_trail', [status(thm)], ['68', '159'])).
% 0.75/0.94  thf('204', plain,
% 0.75/0.94      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 0.75/0.94      inference('clc', [status(thm)], ['202', '203'])).
% 0.75/0.94  thf('205', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ sk_C_1 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['196', '197'])).
% 0.75/0.94  thf('206', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 0.75/0.94      inference('clc', [status(thm)], ['204', '205'])).
% 0.75/0.94  thf('207', plain, ((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 0.75/0.94      inference('demod', [status(thm)], ['174', '206'])).
% 0.75/0.94  thf('208', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.75/0.94      inference('demod', [status(thm)], ['171', '207'])).
% 0.75/0.94  thf('209', plain, ($false), inference('demod', [status(thm)], ['20', '208'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
