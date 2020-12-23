%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.if1sTgj3F7

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 577 expanded)
%              Number of leaves         :   39 ( 188 expanded)
%              Depth                    :   20
%              Number of atoms          :  855 (7023 expanded)
%              Number of equality atoms :   87 ( 507 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X45 @ X42 ) @ ( k2_relset_1 @ X43 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k11_relat_1 @ X24 @ X25 )
        = k1_xboole_0 )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( ( k11_relat_1 @ X30 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k11_relat_1 @ X18 @ X19 )
        = ( k9_relat_1 @ X18 @ ( k1_tarski @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26
        = ( k7_relat_1 @ X26 @ X27 ) )
      | ~ ( v4_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k9_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k11_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k11_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','31','32','33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','37','38','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k9_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X28 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('61',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('63',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('65',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != ( k1_tarski @ X31 ) )
      | ( ( k2_relat_1 @ X32 )
        = ( k1_tarski @ ( k1_funct_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('72',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','74'])).

thf('76',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('79',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.if1sTgj3F7
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:27:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 120 iterations in 0.064s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf(t62_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.53         ( m1_subset_1 @
% 0.21/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.53           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.53            ( m1_subset_1 @
% 0.21/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.53              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t6_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.53       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X42 @ X43)
% 0.21/0.53          | ((X44) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_funct_1 @ X45)
% 0.21/0.53          | ~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.21/0.53          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.21/0.53          | (r2_hidden @ (k1_funct_1 @ X45 @ X42) @ 
% 0.21/0.53             (k2_relset_1 @ X43 @ X44 @ X45)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.21/0.53           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.53          | ((sk_B) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.53         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 0.21/0.53          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.21/0.53         = (k2_relat_1 @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf(t205_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.53         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i]:
% 0.21/0.53         (((k11_relat_1 @ X24 @ X25) = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 0.21/0.53          | ~ (v1_relat_1 @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.21/0.53  thf(t117_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.53         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.21/0.53          | ((k11_relat_1 @ X30 @ X29) = (k1_tarski @ (k1_funct_1 @ X30 @ X29)))
% 0.21/0.53          | ~ (v1_funct_1 @ X30)
% 0.21/0.53          | ~ (v1_relat_1 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1)))
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.21/0.53         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.21/0.53         = (k2_relat_1 @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((((k2_relat_1 @ sk_C_1) != (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.53        | ((k11_relat_1 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 0.21/0.53        | ~ (v1_funct_1 @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf(d16_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i]:
% 0.21/0.53         (((k11_relat_1 @ X18 @ X19) = (k9_relat_1 @ X18 @ (k1_tarski @ X19)))
% 0.21/0.53          | ~ (v1_relat_1 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.53         ((v4_relat_1 @ X36 @ X37)
% 0.21/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('18', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf(t209_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i]:
% 0.21/0.53         (((X26) = (k7_relat_1 @ X26 @ X27))
% 0.21/0.53          | ~ (v4_relat_1 @ X26 @ X27)
% 0.21/0.53          | ~ (v1_relat_1 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_C_1)
% 0.21/0.53        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( v1_relat_1 @ C ) ))).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.53         ((v1_relat_1 @ X33)
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.53  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.53  thf(t148_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i]:
% 0.21/0.53         (((k2_relat_1 @ (k7_relat_1 @ X22 @ X23)) = (k9_relat_1 @ X22 @ X23))
% 0.21/0.53          | ~ (v1_relat_1 @ X22))),
% 0.21/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['15', '28'])).
% 0.21/0.53  thf('30', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('31', plain, (((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('33', plain, (((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 0.21/0.53        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '31', '32', '33', '34'])).
% 0.21/0.53  thf('36', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '36'])).
% 0.21/0.53  thf('38', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('39', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ k1_xboole_0)
% 0.21/0.53          | ((sk_B) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '37', '38', '39'])).
% 0.21/0.53  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ k1_xboole_0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf(t113_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X14 : $i, X15 : $i]:
% 0.21/0.53         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.21/0.53          | ((X15) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.53  thf(t152_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]: ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.53  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('clc', [status(thm)], ['42', '46'])).
% 0.21/0.53  thf('48', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X4 : $i, X6 : $i]:
% 0.21/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf('54', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '53'])).
% 0.21/0.54  thf('55', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         (((k2_relat_1 @ (k7_relat_1 @ X22 @ X23)) = (k9_relat_1 @ X22 @ X23))
% 0.21/0.54          | ~ (v1_relat_1 @ X22))),
% 0.21/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.54  thf(t65_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.54         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X28 : $i]:
% 0.21/0.54         (((k2_relat_1 @ X28) != (k1_xboole_0))
% 0.21/0.54          | ((k1_relat_1 @ X28) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X28))),
% 0.21/0.54      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.54          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_C_1)
% 0.21/0.54        | ((k1_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.21/0.54            = (k1_xboole_0))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.54        | ((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.54  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('61', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.54  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.54        | ((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.54        | ((k2_relat_1 @ sk_C_1) != (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.54  thf('66', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.54        | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.54  thf('68', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.54  thf(t14_funct_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.54         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (![X31 : $i, X32 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X32) != (k1_tarski @ X31))
% 0.21/0.54          | ((k2_relat_1 @ X32) = (k1_tarski @ (k1_funct_1 @ X32 @ X31)))
% 0.21/0.54          | ~ (v1_funct_1 @ X32)
% 0.21/0.54          | ~ (v1_relat_1 @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.54          | ((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.54  thf('71', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('72', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('73', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.54          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['54', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('78', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.54  thf('80', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['76', '79'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
