%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nk8n2CF7UB

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 324 expanded)
%              Number of leaves         :   39 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  986 (3655 expanded)
%              Number of equality atoms :   71 ( 191 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ( X23
       != ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_funct_1 @ X22 @ X21 )
        = k1_xboole_0 )
      | ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X24 ) @ X22 )
      | ( X24
       != ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( k1_funct_1 @ X22 @ X21 ) ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X41 @ X38 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('19',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['7','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['20','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('27',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['25','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('39',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('45',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('47',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('49',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k11_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ X11 @ ( k1_tarski @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k11_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ X11 @ ( k1_tarski @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('55',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45','46','53','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k1_funct_1 @ X22 @ X21 )
        = k1_xboole_0 )
      | ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('68',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X27 ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('78',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('79',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X27 ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('88',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('91',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','92'])).

thf('94',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['93'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['32','94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nk8n2CF7UB
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 107 iterations in 0.057s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.51  thf(d4_funct_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.51       ( ![B:$i,C:$i]:
% 0.19/0.51         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.19/0.51             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.19/0.51               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.51           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.19/0.51             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.19/0.51               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.51         ((r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.19/0.51          | ((X23) = (k1_xboole_0))
% 0.19/0.51          | ((X23) != (k1_funct_1 @ X22 @ X21))
% 0.19/0.51          | ~ (v1_funct_1 @ X22)
% 0.19/0.51          | ~ (v1_relat_1 @ X22))),
% 0.19/0.51      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (![X21 : $i, X22 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X22)
% 0.19/0.51          | ~ (v1_funct_1 @ X22)
% 0.19/0.51          | ((k1_funct_1 @ X22 @ X21) = (k1_xboole_0))
% 0.19/0.51          | (r2_hidden @ X21 @ (k1_relat_1 @ X22)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.19/0.51          | (r2_hidden @ (k4_tarski @ X21 @ X24) @ X22)
% 0.19/0.51          | ((X24) != (k1_funct_1 @ X22 @ X21))
% 0.19/0.51          | ~ (v1_funct_1 @ X22)
% 0.19/0.51          | ~ (v1_relat_1 @ X22))),
% 0.19/0.51      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X21 : $i, X22 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X22)
% 0.19/0.51          | ~ (v1_funct_1 @ X22)
% 0.19/0.51          | (r2_hidden @ (k4_tarski @ X21 @ (k1_funct_1 @ X22 @ X21)) @ X22)
% 0.19/0.51          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X22)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X0 @ X1)) @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.51  thf(d1_xboole_0, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.51  thf(t61_funct_2, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.51         ( m1_subset_1 @
% 0.19/0.51           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.51       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.51         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.51            ( m1_subset_1 @
% 0.19/0.51              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.51          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.51            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t7_funct_2, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.19/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X38 @ X39)
% 0.19/0.51          | ((X40) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_funct_1 @ X41)
% 0.19/0.51          | ~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.19/0.51          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ X41 @ X38) @ X40))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.19/0.51          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.19/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.51          | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf('12', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.19/0.51          | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.19/0.51  thf('15', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.19/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.19/0.51        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.19/0.51           sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '16'])).
% 0.19/0.51  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.19/0.51  thf('18', plain, (![X10 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ sk_B_1)),
% 0.19/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.19/0.51        | ~ (v1_xboole_0 @ sk_C)
% 0.19/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.51        | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.51      inference('sup+', [status(thm)], ['7', '19'])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc1_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( v1_relat_1 @ C ) ))).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.51         ((v1_relat_1 @ X32)
% 0.19/0.51          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.51  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (((r2_hidden @ k1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C))),
% 0.19/0.51      inference('demod', [status(thm)], ['20', '23', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('27', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      ((~ (r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.19/0.51        | ~ (v1_xboole_0 @ sk_C)
% 0.19/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.51        | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      ((~ (r2_hidden @ k1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C))),
% 0.19/0.51      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.19/0.51  thf('32', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.19/0.51      inference('clc', [status(thm)], ['25', '31'])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc2_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.19/0.51         ((v4_relat_1 @ X35 @ X36)
% 0.19/0.51          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.51  thf('35', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.51  thf(t209_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i]:
% 0.19/0.51         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.19/0.51          | ~ (v4_relat_1 @ X17 @ X18)
% 0.19/0.51          | ~ (v1_relat_1 @ X17))),
% 0.19/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.51        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.51  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('39', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.51  thf(t148_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i]:
% 0.19/0.51         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.19/0.51          | ~ (v1_relat_1 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.51  thf(t64_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X19 : $i]:
% 0.19/0.51         (((k2_relat_1 @ X19) != (k1_xboole_0))
% 0.19/0.51          | ((X19) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X1)
% 0.19/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.51          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.51        | ((k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.51        | ((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['39', '42'])).
% 0.19/0.51  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('45', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.51  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf(t69_enumset1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.51  thf('47', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('49', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf(d16_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.19/0.51  thf('50', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i]:
% 0.19/0.51         (((k11_relat_1 @ X11 @ X12) = (k9_relat_1 @ X11 @ (k1_tarski @ X12)))
% 0.19/0.51          | ~ (v1_relat_1 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.19/0.51  thf('51', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X1))),
% 0.19/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k11_relat_1 @ sk_C @ X0)
% 0.19/0.51           = (k9_relat_1 @ sk_C @ (k2_tarski @ X0 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['48', '51'])).
% 0.19/0.51  thf('53', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k11_relat_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['47', '52'])).
% 0.19/0.51  thf('54', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i]:
% 0.19/0.51         (((k11_relat_1 @ X11 @ X12) = (k9_relat_1 @ X11 @ (k1_tarski @ X12)))
% 0.19/0.51          | ~ (v1_relat_1 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.19/0.51  thf('55', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i]:
% 0.19/0.51         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.19/0.51          | ~ (v1_relat_1 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.51      inference('sup+', [status(thm)], ['55', '56'])).
% 0.19/0.51  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('59', plain,
% 0.19/0.51      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.51  thf('60', plain,
% 0.19/0.51      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.51      inference('sup+', [status(thm)], ['54', '59'])).
% 0.19/0.51  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('62', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.51  thf('63', plain,
% 0.19/0.51      ((((sk_C) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['43', '44', '45', '46', '53', '62'])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_C @ 
% 0.19/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('65', plain,
% 0.19/0.51      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.19/0.51         ((v5_relat_1 @ X35 @ X37)
% 0.19/0.51          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.51  thf('66', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.51  thf('67', plain,
% 0.19/0.51      (![X21 : $i, X22 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X22)
% 0.19/0.51          | ~ (v1_funct_1 @ X22)
% 0.19/0.51          | ((k1_funct_1 @ X22 @ X21) = (k1_xboole_0))
% 0.19/0.51          | (r2_hidden @ X21 @ (k1_relat_1 @ X22)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.51  thf(t172_funct_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.51       ( ![C:$i]:
% 0.19/0.51         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.51           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.19/0.51  thf('68', plain,
% 0.19/0.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ X28 @ X27) @ X29)
% 0.19/0.51          | ~ (v1_funct_1 @ X28)
% 0.19/0.51          | ~ (v5_relat_1 @ X28 @ X29)
% 0.19/0.51          | ~ (v1_relat_1 @ X28))),
% 0.19/0.51      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.19/0.51  thf('69', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v5_relat_1 @ X0 @ X2)
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.19/0.51      inference('sup-', [status(thm)], ['67', '68'])).
% 0.19/0.51  thf('70', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.19/0.51          | ~ (v5_relat_1 @ X0 @ X2)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['69'])).
% 0.19/0.51  thf('71', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.51          | ~ (v1_relat_1 @ sk_C)
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['66', '70'])).
% 0.19/0.51  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('74', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.19/0.51  thf('75', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('76', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.51  thf('77', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.51  thf(t205_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.51         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf('78', plain,
% 0.19/0.51      (![X15 : $i, X16 : $i]:
% 0.19/0.51         (((k11_relat_1 @ X15 @ X16) = (k1_xboole_0))
% 0.19/0.51          | (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.19/0.51          | ~ (v1_relat_1 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.19/0.51  thf('79', plain,
% 0.19/0.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ X28 @ X27) @ X29)
% 0.19/0.51          | ~ (v1_funct_1 @ X28)
% 0.19/0.51          | ~ (v5_relat_1 @ X28 @ X29)
% 0.19/0.51          | ~ (v1_relat_1 @ X28))),
% 0.19/0.51      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.19/0.51  thf('80', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v5_relat_1 @ X0 @ X2)
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.19/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.19/0.51  thf('81', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.19/0.51          | ~ (v1_funct_1 @ X0)
% 0.19/0.51          | ~ (v5_relat_1 @ X0 @ X2)
% 0.19/0.51          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['80'])).
% 0.19/0.51  thf('82', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ sk_C)
% 0.19/0.51          | ((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['77', '81'])).
% 0.19/0.51  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('85', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.19/0.51          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.19/0.51  thf('86', plain,
% 0.19/0.51      (((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.19/0.51        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['76', '85'])).
% 0.19/0.51  thf('87', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.51  thf('88', plain,
% 0.19/0.51      (((r2_hidden @ k1_xboole_0 @ sk_B_1)
% 0.19/0.51        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['86', '87'])).
% 0.19/0.51  thf('89', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('90', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.51  thf('91', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.19/0.51      inference('demod', [status(thm)], ['89', '90'])).
% 0.19/0.51  thf('92', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.19/0.51      inference('clc', [status(thm)], ['88', '91'])).
% 0.19/0.51  thf('93', plain,
% 0.19/0.51      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['63', '92'])).
% 0.19/0.51  thf('94', plain, (((sk_C) = (k1_xboole_0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['93'])).
% 0.19/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.51  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.51  thf('96', plain, ($false),
% 0.19/0.51      inference('demod', [status(thm)], ['32', '94', '95'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
