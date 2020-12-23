%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GEhQhl3473

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:08 EST 2020

% Result     : Theorem 6.66s
% Output     : Refutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 927 expanded)
%              Number of leaves         :   45 ( 293 expanded)
%              Depth                    :   18
%              Number of atoms          : 1542 (20722 expanded)
%              Number of equality atoms :   84 ( 367 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('6',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X15 ) )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('16',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('25',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('26',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('27',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','34'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('36',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_funct_2 @ X39 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','45'])).

thf('47',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('48',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('52',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( X45
        = ( k2_funct_1 @ X48 ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X46 @ X46 @ X47 @ X48 @ X45 ) @ ( k6_partfun1 @ X47 ) )
      | ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('66',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('67',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( X45
        = ( k2_funct_1 @ X48 ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X46 @ X46 @ X47 @ X48 @ X45 ) @ ( k6_relat_1 @ X47 ) )
      | ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('81',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('82',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('84',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X29 )
      | ( v2_funct_2 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('85',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['85','86','87'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('89',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_funct_2 @ X31 @ X30 )
      | ( ( k2_relat_1 @ X31 )
        = X30 )
      | ~ ( v5_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('92',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('94',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('95',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('97',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['90','95','98'])).

thf('100',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['82','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X29 )
      | ( v2_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('103',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['73','76','77','78','79','100','106'])).

thf('108',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('110',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('113',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['46','114','115'])).

thf('117',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('118',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','113'])).

thf('122',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','113'])).

thf('123',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('124',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('126',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['120','121','122','124','125'])).

thf('127',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['117','126'])).

thf('128',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['116','127'])).

thf('129',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','113'])).

thf('134',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','113'])).

thf('135',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('136',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('137',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['132','133','134','135','136'])).

thf('138',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['129','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['128','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GEhQhl3473
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:20:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 6.66/6.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.66/6.87  % Solved by: fo/fo7.sh
% 6.66/6.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.66/6.87  % done 5815 iterations in 6.410s
% 6.66/6.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.66/6.87  % SZS output start Refutation
% 6.66/6.87  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.66/6.87  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.66/6.87  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.66/6.87  thf(sk_B_type, type, sk_B: $i > $i).
% 6.66/6.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.66/6.87  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 6.66/6.87  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.66/6.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.66/6.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.66/6.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.66/6.87  thf(sk_A_type, type, sk_A: $i).
% 6.66/6.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.66/6.87  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.66/6.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.66/6.87  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.66/6.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.66/6.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.66/6.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.66/6.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.66/6.87  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 6.66/6.87  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 6.66/6.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.66/6.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.66/6.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.66/6.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.66/6.87  thf(sk_C_type, type, sk_C: $i).
% 6.66/6.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.66/6.87  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.66/6.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.66/6.87  thf(t8_boole, axiom,
% 6.66/6.87    (![A:$i,B:$i]:
% 6.66/6.87     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 6.66/6.87  thf('1', plain,
% 6.66/6.87      (![X3 : $i, X4 : $i]:
% 6.66/6.87         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t8_boole])).
% 6.66/6.87  thf('2', plain,
% 6.66/6.87      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['0', '1'])).
% 6.66/6.87  thf(d1_xboole_0, axiom,
% 6.66/6.87    (![A:$i]:
% 6.66/6.87     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.66/6.87  thf('3', plain,
% 6.66/6.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.66/6.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.66/6.87  thf(t113_zfmisc_1, axiom,
% 6.66/6.87    (![A:$i,B:$i]:
% 6.66/6.87     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.66/6.87       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.66/6.87  thf('4', plain,
% 6.66/6.87      (![X6 : $i, X7 : $i]:
% 6.66/6.87         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.66/6.87  thf('5', plain,
% 6.66/6.87      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 6.66/6.87      inference('simplify', [status(thm)], ['4'])).
% 6.66/6.87  thf(t29_relset_1, axiom,
% 6.66/6.87    (![A:$i]:
% 6.66/6.87     ( m1_subset_1 @
% 6.66/6.87       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 6.66/6.87  thf('6', plain,
% 6.66/6.87      (![X26 : $i]:
% 6.66/6.87         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 6.66/6.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t29_relset_1])).
% 6.66/6.87  thf('7', plain,
% 6.66/6.87      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 6.66/6.87      inference('sup+', [status(thm)], ['5', '6'])).
% 6.66/6.87  thf(t5_subset, axiom,
% 6.66/6.87    (![A:$i,B:$i,C:$i]:
% 6.66/6.87     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 6.66/6.87          ( v1_xboole_0 @ C ) ) ))).
% 6.66/6.87  thf('8', plain,
% 6.66/6.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.66/6.87         (~ (r2_hidden @ X8 @ X9)
% 6.66/6.87          | ~ (v1_xboole_0 @ X10)
% 6.66/6.87          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t5_subset])).
% 6.66/6.87  thf('9', plain,
% 6.66/6.87      (![X0 : $i]:
% 6.66/6.87         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.66/6.87          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 6.66/6.87      inference('sup-', [status(thm)], ['7', '8'])).
% 6.66/6.87  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.66/6.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.66/6.87  thf('11', plain,
% 6.66/6.87      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 6.66/6.87      inference('demod', [status(thm)], ['9', '10'])).
% 6.66/6.87  thf('12', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['3', '11'])).
% 6.66/6.87  thf('13', plain,
% 6.66/6.87      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['0', '1'])).
% 6.66/6.87  thf('14', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['12', '13'])).
% 6.66/6.87  thf(t67_funct_1, axiom,
% 6.66/6.87    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 6.66/6.87  thf('15', plain,
% 6.66/6.87      (![X15 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X15)) = (k6_relat_1 @ X15))),
% 6.66/6.87      inference('cnf', [status(esa)], [t67_funct_1])).
% 6.66/6.87  thf('16', plain, (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 6.66/6.87      inference('sup+', [status(thm)], ['14', '15'])).
% 6.66/6.87  thf('17', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['12', '13'])).
% 6.66/6.87  thf('18', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 6.66/6.87      inference('sup+', [status(thm)], ['16', '17'])).
% 6.66/6.87  thf('19', plain,
% 6.66/6.87      (![X0 : $i]: (((k1_xboole_0) = (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.87      inference('sup+', [status(thm)], ['2', '18'])).
% 6.66/6.87  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.66/6.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.66/6.87  thf('21', plain,
% 6.66/6.87      (![X0 : $i]: ((v1_xboole_0 @ (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.87      inference('sup+', [status(thm)], ['19', '20'])).
% 6.66/6.87  thf('22', plain,
% 6.66/6.87      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['0', '1'])).
% 6.66/6.87  thf('23', plain,
% 6.66/6.87      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['0', '1'])).
% 6.66/6.87  thf('24', plain,
% 6.66/6.87      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['0', '1'])).
% 6.66/6.87  thf('25', plain,
% 6.66/6.87      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 6.66/6.87      inference('sup+', [status(thm)], ['5', '6'])).
% 6.66/6.87  thf('26', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['12', '13'])).
% 6.66/6.87  thf('27', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 6.66/6.87      inference('demod', [status(thm)], ['25', '26'])).
% 6.66/6.87  thf('28', plain,
% 6.66/6.87      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 6.66/6.87      inference('simplify', [status(thm)], ['4'])).
% 6.66/6.87  thf(redefinition_r2_relset_1, axiom,
% 6.66/6.87    (![A:$i,B:$i,C:$i,D:$i]:
% 6.66/6.87     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.66/6.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.66/6.87       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.66/6.87  thf('29', plain,
% 6.66/6.87      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 6.66/6.87         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.66/6.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.66/6.87          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 6.66/6.87          | ((X22) != (X25)))),
% 6.66/6.87      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.66/6.87  thf('30', plain,
% 6.66/6.87      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.66/6.87         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 6.66/6.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.66/6.87      inference('simplify', [status(thm)], ['29'])).
% 6.66/6.87  thf('31', plain,
% 6.66/6.87      (![X0 : $i, X1 : $i]:
% 6.66/6.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.66/6.87          | (r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1))),
% 6.66/6.87      inference('sup-', [status(thm)], ['28', '30'])).
% 6.66/6.87  thf('32', plain,
% 6.66/6.87      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.66/6.87      inference('sup-', [status(thm)], ['27', '31'])).
% 6.66/6.87  thf('33', plain,
% 6.66/6.87      (![X0 : $i, X1 : $i]:
% 6.66/6.87         ((r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 6.66/6.87          | ~ (v1_xboole_0 @ X0))),
% 6.66/6.87      inference('sup+', [status(thm)], ['24', '32'])).
% 6.66/6.87  thf('34', plain,
% 6.66/6.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.66/6.87         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 6.66/6.87          | ~ (v1_xboole_0 @ X0)
% 6.66/6.87          | ~ (v1_xboole_0 @ X1))),
% 6.66/6.87      inference('sup+', [status(thm)], ['23', '33'])).
% 6.66/6.87  thf('35', plain,
% 6.66/6.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.66/6.87         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 6.66/6.87          | ~ (v1_xboole_0 @ X0)
% 6.66/6.87          | ~ (v1_xboole_0 @ X2)
% 6.66/6.87          | ~ (v1_xboole_0 @ X1))),
% 6.66/6.87      inference('sup+', [status(thm)], ['22', '34'])).
% 6.66/6.87  thf(t87_funct_2, conjecture,
% 6.66/6.87    (![A:$i,B:$i]:
% 6.66/6.87     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.66/6.87         ( v3_funct_2 @ B @ A @ A ) & 
% 6.66/6.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.66/6.87       ( ![C:$i]:
% 6.66/6.87         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 6.66/6.87             ( v3_funct_2 @ C @ A @ A ) & 
% 6.66/6.87             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.66/6.87           ( ( r2_relset_1 @
% 6.66/6.87               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 6.66/6.87               ( k6_partfun1 @ A ) ) =>
% 6.66/6.87             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 6.66/6.87  thf(zf_stmt_0, negated_conjecture,
% 6.66/6.87    (~( ![A:$i,B:$i]:
% 6.66/6.87        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.66/6.87            ( v3_funct_2 @ B @ A @ A ) & 
% 6.66/6.87            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.66/6.87          ( ![C:$i]:
% 6.66/6.87            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 6.66/6.87                ( v3_funct_2 @ C @ A @ A ) & 
% 6.66/6.87                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.66/6.87              ( ( r2_relset_1 @
% 6.66/6.87                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 6.66/6.87                  ( k6_partfun1 @ A ) ) =>
% 6.66/6.87                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 6.66/6.87    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 6.66/6.87  thf('36', plain,
% 6.66/6.87      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('37', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf(redefinition_k2_funct_2, axiom,
% 6.66/6.87    (![A:$i,B:$i]:
% 6.66/6.87     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.66/6.87         ( v3_funct_2 @ B @ A @ A ) & 
% 6.66/6.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.66/6.87       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 6.66/6.87  thf('38', plain,
% 6.66/6.87      (![X38 : $i, X39 : $i]:
% 6.66/6.87         (((k2_funct_2 @ X39 @ X38) = (k2_funct_1 @ X38))
% 6.66/6.87          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 6.66/6.87          | ~ (v3_funct_2 @ X38 @ X39 @ X39)
% 6.66/6.87          | ~ (v1_funct_2 @ X38 @ X39 @ X39)
% 6.66/6.87          | ~ (v1_funct_1 @ X38))),
% 6.66/6.87      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 6.66/6.87  thf('39', plain,
% 6.66/6.87      ((~ (v1_funct_1 @ sk_B_1)
% 6.66/6.87        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 6.66/6.87        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 6.66/6.87        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 6.66/6.87      inference('sup-', [status(thm)], ['37', '38'])).
% 6.66/6.87  thf('40', plain, ((v1_funct_1 @ sk_B_1)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('41', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('42', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('43', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 6.66/6.87      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 6.66/6.87  thf('44', plain,
% 6.66/6.87      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 6.66/6.87      inference('demod', [status(thm)], ['36', '43'])).
% 6.66/6.87  thf('45', plain,
% 6.66/6.87      ((~ (v1_xboole_0 @ sk_C)
% 6.66/6.87        | ~ (v1_xboole_0 @ sk_A)
% 6.66/6.87        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B_1)))),
% 6.66/6.87      inference('sup-', [status(thm)], ['35', '44'])).
% 6.66/6.87  thf('46', plain,
% 6.66/6.87      ((~ (v1_xboole_0 @ sk_B_1)
% 6.66/6.87        | ~ (v1_xboole_0 @ sk_A)
% 6.66/6.87        | ~ (v1_xboole_0 @ sk_C))),
% 6.66/6.87      inference('sup-', [status(thm)], ['21', '45'])).
% 6.66/6.87  thf('47', plain,
% 6.66/6.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.66/6.87        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 6.66/6.87        (k6_partfun1 @ sk_A))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf(redefinition_k6_partfun1, axiom,
% 6.66/6.87    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.66/6.87  thf('48', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 6.66/6.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.66/6.87  thf('49', plain,
% 6.66/6.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.66/6.87        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 6.66/6.87        (k6_relat_1 @ sk_A))),
% 6.66/6.87      inference('demod', [status(thm)], ['47', '48'])).
% 6.66/6.87  thf('50', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('51', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf(dt_k1_partfun1, axiom,
% 6.66/6.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.66/6.87     ( ( ( v1_funct_1 @ E ) & 
% 6.66/6.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.66/6.87         ( v1_funct_1 @ F ) & 
% 6.66/6.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.66/6.87       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 6.66/6.87         ( m1_subset_1 @
% 6.66/6.87           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.66/6.87           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 6.66/6.87  thf('52', plain,
% 6.66/6.87      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 6.66/6.87         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 6.66/6.87          | ~ (v1_funct_1 @ X32)
% 6.66/6.87          | ~ (v1_funct_1 @ X35)
% 6.66/6.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 6.66/6.87          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 6.66/6.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 6.66/6.87      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.66/6.87  thf('53', plain,
% 6.66/6.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.66/6.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1) @ 
% 6.66/6.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.66/6.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.66/6.87          | ~ (v1_funct_1 @ X1)
% 6.66/6.87          | ~ (v1_funct_1 @ sk_B_1))),
% 6.66/6.87      inference('sup-', [status(thm)], ['51', '52'])).
% 6.66/6.87  thf('54', plain, ((v1_funct_1 @ sk_B_1)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('55', plain,
% 6.66/6.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.66/6.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1) @ 
% 6.66/6.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.66/6.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.66/6.87          | ~ (v1_funct_1 @ X1))),
% 6.66/6.87      inference('demod', [status(thm)], ['53', '54'])).
% 6.66/6.87  thf('56', plain,
% 6.66/6.87      ((~ (v1_funct_1 @ sk_C)
% 6.66/6.87        | (m1_subset_1 @ 
% 6.66/6.87           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 6.66/6.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.66/6.87      inference('sup-', [status(thm)], ['50', '55'])).
% 6.66/6.87  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('58', plain,
% 6.66/6.87      ((m1_subset_1 @ 
% 6.66/6.87        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 6.66/6.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('demod', [status(thm)], ['56', '57'])).
% 6.66/6.87  thf('59', plain,
% 6.66/6.87      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 6.66/6.87         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.66/6.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 6.66/6.87          | ((X22) = (X25))
% 6.66/6.87          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 6.66/6.87      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.66/6.87  thf('60', plain,
% 6.66/6.87      (![X0 : $i]:
% 6.66/6.87         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.66/6.87             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ X0)
% 6.66/6.87          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) = (X0))
% 6.66/6.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.66/6.87      inference('sup-', [status(thm)], ['58', '59'])).
% 6.66/6.87  thf('61', plain,
% 6.66/6.87      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 6.66/6.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.66/6.87        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 6.66/6.87            = (k6_relat_1 @ sk_A)))),
% 6.66/6.87      inference('sup-', [status(thm)], ['49', '60'])).
% 6.66/6.87  thf('62', plain,
% 6.66/6.87      (![X26 : $i]:
% 6.66/6.87         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 6.66/6.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t29_relset_1])).
% 6.66/6.87  thf('63', plain,
% 6.66/6.87      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 6.66/6.87         = (k6_relat_1 @ sk_A))),
% 6.66/6.87      inference('demod', [status(thm)], ['61', '62'])).
% 6.66/6.87  thf('64', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf(t36_funct_2, axiom,
% 6.66/6.87    (![A:$i,B:$i,C:$i]:
% 6.66/6.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.66/6.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.66/6.87       ( ![D:$i]:
% 6.66/6.87         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.66/6.87             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.66/6.87           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 6.66/6.87               ( r2_relset_1 @
% 6.66/6.87                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.66/6.87                 ( k6_partfun1 @ A ) ) & 
% 6.66/6.87               ( v2_funct_1 @ C ) ) =>
% 6.66/6.87             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.66/6.87               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 6.66/6.87  thf('65', plain,
% 6.66/6.87      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 6.66/6.87         (~ (v1_funct_1 @ X45)
% 6.66/6.87          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 6.66/6.87          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 6.66/6.87          | ((X45) = (k2_funct_1 @ X48))
% 6.66/6.87          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 6.66/6.87               (k1_partfun1 @ X47 @ X46 @ X46 @ X47 @ X48 @ X45) @ 
% 6.66/6.87               (k6_partfun1 @ X47))
% 6.66/6.87          | ((X46) = (k1_xboole_0))
% 6.66/6.87          | ((X47) = (k1_xboole_0))
% 6.66/6.87          | ~ (v2_funct_1 @ X48)
% 6.66/6.87          | ((k2_relset_1 @ X47 @ X46 @ X48) != (X46))
% 6.66/6.87          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 6.66/6.87          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 6.66/6.87          | ~ (v1_funct_1 @ X48))),
% 6.66/6.87      inference('cnf', [status(esa)], [t36_funct_2])).
% 6.66/6.87  thf('66', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 6.66/6.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.66/6.87  thf('67', plain,
% 6.66/6.87      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 6.66/6.87         (~ (v1_funct_1 @ X45)
% 6.66/6.87          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 6.66/6.87          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 6.66/6.87          | ((X45) = (k2_funct_1 @ X48))
% 6.66/6.87          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 6.66/6.87               (k1_partfun1 @ X47 @ X46 @ X46 @ X47 @ X48 @ X45) @ 
% 6.66/6.87               (k6_relat_1 @ X47))
% 6.66/6.87          | ((X46) = (k1_xboole_0))
% 6.66/6.87          | ((X47) = (k1_xboole_0))
% 6.66/6.87          | ~ (v2_funct_1 @ X48)
% 6.66/6.87          | ((k2_relset_1 @ X47 @ X46 @ X48) != (X46))
% 6.66/6.87          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 6.66/6.87          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 6.66/6.87          | ~ (v1_funct_1 @ X48))),
% 6.66/6.87      inference('demod', [status(thm)], ['65', '66'])).
% 6.66/6.87  thf('68', plain,
% 6.66/6.87      (![X0 : $i]:
% 6.66/6.87         (~ (v1_funct_1 @ X0)
% 6.66/6.87          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 6.66/6.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.66/6.87          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 6.66/6.87          | ~ (v2_funct_1 @ X0)
% 6.66/6.87          | ((sk_A) = (k1_xboole_0))
% 6.66/6.87          | ((sk_A) = (k1_xboole_0))
% 6.66/6.87          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.66/6.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 6.66/6.87               (k6_relat_1 @ sk_A))
% 6.66/6.87          | ((sk_C) = (k2_funct_1 @ X0))
% 6.66/6.87          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 6.66/6.87          | ~ (v1_funct_1 @ sk_C))),
% 6.66/6.87      inference('sup-', [status(thm)], ['64', '67'])).
% 6.66/6.87  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('71', plain,
% 6.66/6.87      (![X0 : $i]:
% 6.66/6.87         (~ (v1_funct_1 @ X0)
% 6.66/6.87          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 6.66/6.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.66/6.87          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 6.66/6.87          | ~ (v2_funct_1 @ X0)
% 6.66/6.87          | ((sk_A) = (k1_xboole_0))
% 6.66/6.87          | ((sk_A) = (k1_xboole_0))
% 6.66/6.87          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.66/6.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 6.66/6.87               (k6_relat_1 @ sk_A))
% 6.66/6.87          | ((sk_C) = (k2_funct_1 @ X0)))),
% 6.66/6.87      inference('demod', [status(thm)], ['68', '69', '70'])).
% 6.66/6.87  thf('72', plain,
% 6.66/6.87      (![X0 : $i]:
% 6.66/6.87         (((sk_C) = (k2_funct_1 @ X0))
% 6.66/6.87          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.66/6.87               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 6.66/6.87               (k6_relat_1 @ sk_A))
% 6.66/6.87          | ((sk_A) = (k1_xboole_0))
% 6.66/6.87          | ~ (v2_funct_1 @ X0)
% 6.66/6.87          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 6.66/6.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.66/6.87          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 6.66/6.87          | ~ (v1_funct_1 @ X0))),
% 6.66/6.87      inference('simplify', [status(thm)], ['71'])).
% 6.66/6.87  thf('73', plain,
% 6.66/6.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 6.66/6.87           (k6_relat_1 @ sk_A))
% 6.66/6.87        | ~ (v1_funct_1 @ sk_B_1)
% 6.66/6.87        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 6.66/6.87        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.66/6.87        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) != (sk_A))
% 6.66/6.87        | ~ (v2_funct_1 @ sk_B_1)
% 6.66/6.87        | ((sk_A) = (k1_xboole_0))
% 6.66/6.87        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 6.66/6.87      inference('sup-', [status(thm)], ['63', '72'])).
% 6.66/6.87  thf('74', plain,
% 6.66/6.87      (![X26 : $i]:
% 6.66/6.87         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 6.66/6.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t29_relset_1])).
% 6.66/6.87  thf('75', plain,
% 6.66/6.87      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.66/6.87         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 6.66/6.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.66/6.87      inference('simplify', [status(thm)], ['29'])).
% 6.66/6.87  thf('76', plain,
% 6.66/6.87      (![X0 : $i]:
% 6.66/6.87         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 6.66/6.87      inference('sup-', [status(thm)], ['74', '75'])).
% 6.66/6.87  thf('77', plain, ((v1_funct_1 @ sk_B_1)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('78', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('79', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('80', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf(redefinition_k2_relset_1, axiom,
% 6.66/6.87    (![A:$i,B:$i,C:$i]:
% 6.66/6.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.66/6.87       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.66/6.87  thf('81', plain,
% 6.66/6.87      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.66/6.87         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 6.66/6.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 6.66/6.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.66/6.87  thf('82', plain,
% 6.66/6.87      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 6.66/6.87      inference('sup-', [status(thm)], ['80', '81'])).
% 6.66/6.87  thf('83', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf(cc2_funct_2, axiom,
% 6.66/6.87    (![A:$i,B:$i,C:$i]:
% 6.66/6.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.66/6.87       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 6.66/6.87         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 6.66/6.87  thf('84', plain,
% 6.66/6.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.66/6.87         (~ (v1_funct_1 @ X27)
% 6.66/6.87          | ~ (v3_funct_2 @ X27 @ X28 @ X29)
% 6.66/6.87          | (v2_funct_2 @ X27 @ X29)
% 6.66/6.87          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 6.66/6.87      inference('cnf', [status(esa)], [cc2_funct_2])).
% 6.66/6.87  thf('85', plain,
% 6.66/6.87      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 6.66/6.87        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 6.66/6.87        | ~ (v1_funct_1 @ sk_B_1))),
% 6.66/6.87      inference('sup-', [status(thm)], ['83', '84'])).
% 6.66/6.87  thf('86', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('87', plain, ((v1_funct_1 @ sk_B_1)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('88', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 6.66/6.87      inference('demod', [status(thm)], ['85', '86', '87'])).
% 6.66/6.87  thf(d3_funct_2, axiom,
% 6.66/6.87    (![A:$i,B:$i]:
% 6.66/6.87     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 6.66/6.87       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 6.66/6.87  thf('89', plain,
% 6.66/6.87      (![X30 : $i, X31 : $i]:
% 6.66/6.87         (~ (v2_funct_2 @ X31 @ X30)
% 6.66/6.87          | ((k2_relat_1 @ X31) = (X30))
% 6.66/6.87          | ~ (v5_relat_1 @ X31 @ X30)
% 6.66/6.87          | ~ (v1_relat_1 @ X31))),
% 6.66/6.87      inference('cnf', [status(esa)], [d3_funct_2])).
% 6.66/6.87  thf('90', plain,
% 6.66/6.87      ((~ (v1_relat_1 @ sk_B_1)
% 6.66/6.87        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 6.66/6.87        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 6.66/6.87      inference('sup-', [status(thm)], ['88', '89'])).
% 6.66/6.87  thf('91', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf(cc2_relat_1, axiom,
% 6.66/6.87    (![A:$i]:
% 6.66/6.87     ( ( v1_relat_1 @ A ) =>
% 6.66/6.87       ( ![B:$i]:
% 6.66/6.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.66/6.87  thf('92', plain,
% 6.66/6.87      (![X11 : $i, X12 : $i]:
% 6.66/6.87         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 6.66/6.87          | (v1_relat_1 @ X11)
% 6.66/6.87          | ~ (v1_relat_1 @ X12))),
% 6.66/6.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.66/6.87  thf('93', plain,
% 6.66/6.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 6.66/6.87      inference('sup-', [status(thm)], ['91', '92'])).
% 6.66/6.87  thf(fc6_relat_1, axiom,
% 6.66/6.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.66/6.87  thf('94', plain,
% 6.66/6.87      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 6.66/6.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.66/6.87  thf('95', plain, ((v1_relat_1 @ sk_B_1)),
% 6.66/6.87      inference('demod', [status(thm)], ['93', '94'])).
% 6.66/6.87  thf('96', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf(cc2_relset_1, axiom,
% 6.66/6.87    (![A:$i,B:$i,C:$i]:
% 6.66/6.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.66/6.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.66/6.87  thf('97', plain,
% 6.66/6.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.66/6.87         ((v5_relat_1 @ X16 @ X18)
% 6.66/6.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 6.66/6.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.66/6.87  thf('98', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 6.66/6.87      inference('sup-', [status(thm)], ['96', '97'])).
% 6.66/6.87  thf('99', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 6.66/6.87      inference('demod', [status(thm)], ['90', '95', '98'])).
% 6.66/6.87  thf('100', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A))),
% 6.66/6.87      inference('demod', [status(thm)], ['82', '99'])).
% 6.66/6.87  thf('101', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('102', plain,
% 6.66/6.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.66/6.87         (~ (v1_funct_1 @ X27)
% 6.66/6.87          | ~ (v3_funct_2 @ X27 @ X28 @ X29)
% 6.66/6.87          | (v2_funct_1 @ X27)
% 6.66/6.87          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 6.66/6.87      inference('cnf', [status(esa)], [cc2_funct_2])).
% 6.66/6.87  thf('103', plain,
% 6.66/6.87      (((v2_funct_1 @ sk_B_1)
% 6.66/6.87        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 6.66/6.87        | ~ (v1_funct_1 @ sk_B_1))),
% 6.66/6.87      inference('sup-', [status(thm)], ['101', '102'])).
% 6.66/6.87  thf('104', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('105', plain, ((v1_funct_1 @ sk_B_1)),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('106', plain, ((v2_funct_1 @ sk_B_1)),
% 6.66/6.87      inference('demod', [status(thm)], ['103', '104', '105'])).
% 6.66/6.87  thf('107', plain,
% 6.66/6.87      ((((sk_A) != (sk_A))
% 6.66/6.87        | ((sk_A) = (k1_xboole_0))
% 6.66/6.87        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 6.66/6.87      inference('demod', [status(thm)],
% 6.66/6.87                ['73', '76', '77', '78', '79', '100', '106'])).
% 6.66/6.87  thf('108', plain,
% 6.66/6.87      ((((sk_C) = (k2_funct_1 @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 6.66/6.87      inference('simplify', [status(thm)], ['107'])).
% 6.66/6.87  thf('109', plain,
% 6.66/6.87      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 6.66/6.87      inference('demod', [status(thm)], ['36', '43'])).
% 6.66/6.87  thf('110', plain,
% 6.66/6.87      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 6.66/6.87      inference('sup-', [status(thm)], ['108', '109'])).
% 6.66/6.87  thf('111', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('112', plain,
% 6.66/6.87      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.66/6.87         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 6.66/6.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.66/6.87      inference('simplify', [status(thm)], ['29'])).
% 6.66/6.87  thf('113', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 6.66/6.87      inference('sup-', [status(thm)], ['111', '112'])).
% 6.66/6.87  thf('114', plain, (((sk_A) = (k1_xboole_0))),
% 6.66/6.87      inference('demod', [status(thm)], ['110', '113'])).
% 6.66/6.87  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.66/6.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.66/6.87  thf('116', plain, ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C))),
% 6.66/6.87      inference('demod', [status(thm)], ['46', '114', '115'])).
% 6.66/6.87  thf('117', plain,
% 6.66/6.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.66/6.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.66/6.87  thf('118', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('119', plain,
% 6.66/6.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.66/6.87         (~ (r2_hidden @ X8 @ X9)
% 6.66/6.87          | ~ (v1_xboole_0 @ X10)
% 6.66/6.87          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t5_subset])).
% 6.66/6.87  thf('120', plain,
% 6.66/6.87      (![X0 : $i]:
% 6.66/6.87         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 6.66/6.87          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 6.66/6.87      inference('sup-', [status(thm)], ['118', '119'])).
% 6.66/6.87  thf('121', plain, (((sk_A) = (k1_xboole_0))),
% 6.66/6.87      inference('demod', [status(thm)], ['110', '113'])).
% 6.66/6.87  thf('122', plain, (((sk_A) = (k1_xboole_0))),
% 6.66/6.87      inference('demod', [status(thm)], ['110', '113'])).
% 6.66/6.87  thf('123', plain,
% 6.66/6.87      (![X6 : $i, X7 : $i]:
% 6.66/6.87         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.66/6.87  thf('124', plain,
% 6.66/6.87      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 6.66/6.87      inference('simplify', [status(thm)], ['123'])).
% 6.66/6.87  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.66/6.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.66/6.87  thf('126', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 6.66/6.87      inference('demod', [status(thm)], ['120', '121', '122', '124', '125'])).
% 6.66/6.87  thf('127', plain, ((v1_xboole_0 @ sk_B_1)),
% 6.66/6.87      inference('sup-', [status(thm)], ['117', '126'])).
% 6.66/6.87  thf('128', plain, (~ (v1_xboole_0 @ sk_C)),
% 6.66/6.87      inference('demod', [status(thm)], ['116', '127'])).
% 6.66/6.87  thf('129', plain,
% 6.66/6.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.66/6.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.66/6.87  thf('130', plain,
% 6.66/6.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.66/6.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.87  thf('131', plain,
% 6.66/6.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.66/6.87         (~ (r2_hidden @ X8 @ X9)
% 6.66/6.87          | ~ (v1_xboole_0 @ X10)
% 6.66/6.87          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 6.66/6.87      inference('cnf', [status(esa)], [t5_subset])).
% 6.66/6.87  thf('132', plain,
% 6.66/6.87      (![X0 : $i]:
% 6.66/6.87         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 6.66/6.87          | ~ (r2_hidden @ X0 @ sk_C))),
% 6.66/6.87      inference('sup-', [status(thm)], ['130', '131'])).
% 6.66/6.87  thf('133', plain, (((sk_A) = (k1_xboole_0))),
% 6.66/6.87      inference('demod', [status(thm)], ['110', '113'])).
% 6.66/6.87  thf('134', plain, (((sk_A) = (k1_xboole_0))),
% 6.66/6.87      inference('demod', [status(thm)], ['110', '113'])).
% 6.66/6.87  thf('135', plain,
% 6.66/6.87      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 6.66/6.87      inference('simplify', [status(thm)], ['123'])).
% 6.66/6.87  thf('136', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.66/6.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.66/6.87  thf('137', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 6.66/6.87      inference('demod', [status(thm)], ['132', '133', '134', '135', '136'])).
% 6.66/6.87  thf('138', plain, ((v1_xboole_0 @ sk_C)),
% 6.66/6.87      inference('sup-', [status(thm)], ['129', '137'])).
% 6.66/6.87  thf('139', plain, ($false), inference('demod', [status(thm)], ['128', '138'])).
% 6.66/6.87  
% 6.66/6.87  % SZS output end Refutation
% 6.66/6.87  
% 6.66/6.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
