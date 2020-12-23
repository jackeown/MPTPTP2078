%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mxgmxWFY1Q

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:17 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 293 expanded)
%              Number of leaves         :   43 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          : 1167 (5502 expanded)
%              Number of equality atoms :   46 (  78 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('16',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('21',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44 ) )
      | ( v2_funct_1 @ X48 )
      | ( X46 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('28',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29','30','31','32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('36',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('42',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( sk_B @ sk_C ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['43','45','46'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('48',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('49',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('52',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['2','47','52'])).

thf('54',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('59',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_partfun1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('67',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['64','68','71','72','73','74'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('76',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('77',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['64','68','71','72','73','74'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['78','81','82','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['56','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mxgmxWFY1Q
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:26:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.41/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.57  % Solved by: fo/fo7.sh
% 0.41/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.57  % done 394 iterations in 0.127s
% 0.41/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.57  % SZS output start Refutation
% 0.41/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.41/0.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.41/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.41/0.57  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.41/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.57  thf(t29_funct_2, conjecture,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.57       ( ![D:$i]:
% 0.41/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.41/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.41/0.57           ( ( r2_relset_1 @
% 0.41/0.57               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.41/0.57               ( k6_partfun1 @ A ) ) =>
% 0.41/0.57             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.41/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.57          ( ![D:$i]:
% 0.41/0.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.41/0.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.41/0.57              ( ( r2_relset_1 @
% 0.41/0.57                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.41/0.57                  ( k6_partfun1 @ A ) ) =>
% 0.41/0.57                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.41/0.57    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.41/0.57  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('1', plain,
% 0.41/0.57      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.41/0.57      inference('split', [status(esa)], ['0'])).
% 0.41/0.57  thf('2', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.41/0.57      inference('split', [status(esa)], ['0'])).
% 0.41/0.57  thf('3', plain,
% 0.41/0.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.57        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.57        (k6_partfun1 @ sk_A))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('4', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('5', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(dt_k1_partfun1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.57     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.57         ( v1_funct_1 @ F ) & 
% 0.41/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.41/0.57       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.41/0.57         ( m1_subset_1 @
% 0.41/0.57           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.41/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.41/0.57  thf('6', plain,
% 0.41/0.57      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.41/0.57          | ~ (v1_funct_1 @ X33)
% 0.41/0.57          | ~ (v1_funct_1 @ X36)
% 0.41/0.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.41/0.57          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 0.41/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 0.41/0.57      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.41/0.57  thf('7', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.41/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.41/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.41/0.57          | ~ (v1_funct_1 @ X1)
% 0.41/0.57          | ~ (v1_funct_1 @ sk_C))),
% 0.41/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.57  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('9', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.41/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.41/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.41/0.57          | ~ (v1_funct_1 @ X1))),
% 0.41/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.57  thf('10', plain,
% 0.41/0.57      ((~ (v1_funct_1 @ sk_D)
% 0.41/0.57        | (m1_subset_1 @ 
% 0.41/0.57           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['4', '9'])).
% 0.41/0.57  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('12', plain,
% 0.41/0.57      ((m1_subset_1 @ 
% 0.41/0.57        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.41/0.57  thf(redefinition_r2_relset_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.41/0.57  thf('13', plain,
% 0.41/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.57          | ((X20) = (X23))
% 0.41/0.57          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.41/0.57  thf('14', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.57             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 0.41/0.57          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.57  thf('15', plain,
% 0.41/0.57      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.41/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.41/0.57        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.41/0.57            = (k6_partfun1 @ sk_A)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['3', '14'])).
% 0.41/0.57  thf(t29_relset_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( m1_subset_1 @
% 0.41/0.57       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.41/0.57  thf('16', plain,
% 0.41/0.57      (![X24 : $i]:
% 0.41/0.57         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 0.41/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.41/0.57  thf(redefinition_k6_partfun1, axiom,
% 0.41/0.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.41/0.57  thf('17', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.41/0.57  thf('18', plain,
% 0.41/0.57      (![X24 : $i]:
% 0.41/0.57         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.41/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.41/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.57  thf('19', plain,
% 0.41/0.57      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.41/0.57         = (k6_partfun1 @ sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['15', '18'])).
% 0.41/0.57  thf('20', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t26_funct_2, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.57       ( ![E:$i]:
% 0.41/0.57         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.41/0.57             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.41/0.57           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.41/0.57             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.41/0.57               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.41/0.57  thf('21', plain,
% 0.41/0.57      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X44)
% 0.41/0.57          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.41/0.57          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.41/0.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 0.41/0.57          | (v2_funct_1 @ X48)
% 0.41/0.57          | ((X46) = (k1_xboole_0))
% 0.41/0.57          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.41/0.57          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 0.41/0.57          | ~ (v1_funct_1 @ X48))),
% 0.41/0.57      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.41/0.57  thf('22', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X0)
% 0.41/0.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.41/0.57          | ((sk_A) = (k1_xboole_0))
% 0.41/0.57          | (v2_funct_1 @ X0)
% 0.41/0.57          | ~ (v2_funct_1 @ 
% 0.41/0.57               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 0.41/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.41/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.41/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.57  thf('23', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('25', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X0)
% 0.41/0.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.41/0.57          | ((sk_A) = (k1_xboole_0))
% 0.41/0.57          | (v2_funct_1 @ X0)
% 0.41/0.57          | ~ (v2_funct_1 @ 
% 0.41/0.57               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 0.41/0.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.41/0.57  thf('26', plain,
% 0.41/0.57      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.41/0.57        | (v2_funct_1 @ sk_C)
% 0.41/0.57        | ((sk_A) = (k1_xboole_0))
% 0.41/0.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.41/0.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.41/0.57        | ~ (v1_funct_1 @ sk_C))),
% 0.41/0.57      inference('sup-', [status(thm)], ['19', '25'])).
% 0.41/0.57  thf(fc4_funct_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.41/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.41/0.57  thf('27', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 0.41/0.57      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.41/0.57  thf('28', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.41/0.57  thf('29', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 0.41/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.41/0.57  thf('30', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('33', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.41/0.57      inference('demod', [status(thm)], ['26', '29', '30', '31', '32'])).
% 0.41/0.57  thf('34', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.41/0.57      inference('split', [status(esa)], ['0'])).
% 0.41/0.57  thf('35', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.57  thf(t6_mcart_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.41/0.57          ( ![B:$i]:
% 0.41/0.57            ( ~( ( r2_hidden @ B @ A ) & 
% 0.41/0.57                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.41/0.57                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.41/0.57                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.41/0.57                       ( r2_hidden @ G @ B ) ) =>
% 0.41/0.57                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.57  thf('36', plain,
% 0.41/0.57      (![X25 : $i]:
% 0.41/0.57         (((X25) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X25) @ X25))),
% 0.41/0.57      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.41/0.57  thf('37', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(l3_subset_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.41/0.57  thf('38', plain,
% 0.41/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.57         (~ (r2_hidden @ X4 @ X5)
% 0.41/0.57          | (r2_hidden @ X4 @ X6)
% 0.41/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.41/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.41/0.57  thf('39', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.41/0.57          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.41/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.57  thf('40', plain,
% 0.41/0.57      ((((sk_C) = (k1_xboole_0))
% 0.41/0.57        | (r2_hidden @ (sk_B @ sk_C) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['36', '39'])).
% 0.41/0.57  thf(t7_ordinal1, axiom,
% 0.41/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.57  thf('41', plain,
% 0.41/0.57      (![X9 : $i, X10 : $i]:
% 0.41/0.57         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.41/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.57  thf('42', plain,
% 0.41/0.57      ((((sk_C) = (k1_xboole_0))
% 0.41/0.57        | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_C)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.57  thf('43', plain,
% 0.41/0.57      (((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ (sk_B @ sk_C))
% 0.41/0.57         | ((sk_C) = (k1_xboole_0)))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['35', '42'])).
% 0.41/0.57  thf(t113_zfmisc_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.57  thf('44', plain,
% 0.41/0.57      (![X2 : $i, X3 : $i]:
% 0.41/0.57         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.41/0.57  thf('45', plain,
% 0.41/0.57      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.41/0.57      inference('simplify', [status(thm)], ['44'])).
% 0.41/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.57  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.57  thf('47', plain, ((((sk_C) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.41/0.57      inference('demod', [status(thm)], ['43', '45', '46'])).
% 0.41/0.57  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.41/0.57  thf('48', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.41/0.57  thf('49', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.41/0.57  thf('50', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.41/0.57  thf('51', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 0.41/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.41/0.57  thf('52', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.41/0.57      inference('sup+', [status(thm)], ['50', '51'])).
% 0.41/0.57  thf('53', plain, (((v2_funct_1 @ sk_C))),
% 0.41/0.57      inference('demod', [status(thm)], ['2', '47', '52'])).
% 0.41/0.57  thf('54', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 0.41/0.57      inference('split', [status(esa)], ['0'])).
% 0.41/0.57  thf('55', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.41/0.57      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 0.41/0.57  thf('56', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 0.41/0.57      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.41/0.57  thf('57', plain,
% 0.41/0.57      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.41/0.57         = (k6_partfun1 @ sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['15', '18'])).
% 0.41/0.57  thf('58', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t24_funct_2, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.57       ( ![D:$i]:
% 0.41/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.41/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.41/0.57           ( ( r2_relset_1 @
% 0.41/0.57               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.41/0.57               ( k6_partfun1 @ B ) ) =>
% 0.41/0.57             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.41/0.57  thf('59', plain,
% 0.41/0.57      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X40)
% 0.41/0.57          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.41/0.57          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.41/0.57          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 0.41/0.57               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 0.41/0.57               (k6_partfun1 @ X41))
% 0.41/0.57          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 0.41/0.57          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.41/0.57          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 0.41/0.57          | ~ (v1_funct_1 @ X43))),
% 0.41/0.57      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.41/0.57  thf('60', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X0)
% 0.41/0.57          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.41/0.57          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.41/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.57               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.41/0.57               (k6_partfun1 @ sk_A))
% 0.41/0.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.41/0.57          | ~ (v1_funct_1 @ sk_C))),
% 0.41/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.57  thf('61', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('63', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X0)
% 0.41/0.57          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.41/0.57          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.41/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.41/0.57               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.41/0.57               (k6_partfun1 @ sk_A)))),
% 0.41/0.57      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.41/0.57  thf('64', plain,
% 0.41/0.57      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.41/0.57           (k6_partfun1 @ sk_A))
% 0.41/0.57        | ((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 0.41/0.57        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.41/0.57        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.41/0.57        | ~ (v1_funct_1 @ sk_D))),
% 0.41/0.57      inference('sup-', [status(thm)], ['57', '63'])).
% 0.41/0.57  thf('65', plain,
% 0.41/0.57      (![X24 : $i]:
% 0.41/0.57         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.41/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.41/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.57  thf('66', plain,
% 0.41/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.57          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.41/0.57          | ((X20) != (X23)))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.41/0.57  thf('67', plain,
% 0.41/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.57         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.41/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.41/0.57      inference('simplify', [status(thm)], ['66'])).
% 0.41/0.57  thf('68', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.41/0.57      inference('sup-', [status(thm)], ['65', '67'])).
% 0.41/0.57  thf('69', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.57  thf('70', plain,
% 0.41/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.57         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.41/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.57  thf('71', plain,
% 0.41/0.57      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.41/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.57  thf('72', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('73', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('75', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['64', '68', '71', '72', '73', '74'])).
% 0.41/0.57  thf(d3_funct_2, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.41/0.57       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.41/0.57  thf('76', plain,
% 0.41/0.57      (![X31 : $i, X32 : $i]:
% 0.41/0.57         (((k2_relat_1 @ X32) != (X31))
% 0.41/0.57          | (v2_funct_2 @ X32 @ X31)
% 0.41/0.57          | ~ (v5_relat_1 @ X32 @ X31)
% 0.41/0.57          | ~ (v1_relat_1 @ X32))),
% 0.41/0.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.41/0.57  thf('77', plain,
% 0.41/0.57      (![X32 : $i]:
% 0.41/0.57         (~ (v1_relat_1 @ X32)
% 0.41/0.57          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 0.41/0.57          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 0.41/0.57      inference('simplify', [status(thm)], ['76'])).
% 0.41/0.57  thf('78', plain,
% 0.41/0.57      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.41/0.57        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.41/0.57        | ~ (v1_relat_1 @ sk_D))),
% 0.41/0.57      inference('sup-', [status(thm)], ['75', '77'])).
% 0.41/0.57  thf('79', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(cc2_relset_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.57  thf('80', plain,
% 0.41/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.57         ((v5_relat_1 @ X14 @ X16)
% 0.41/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.41/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.57  thf('81', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.41/0.57      inference('sup-', [status(thm)], ['79', '80'])).
% 0.41/0.57  thf('82', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['64', '68', '71', '72', '73', '74'])).
% 0.41/0.57  thf('83', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(cc1_relset_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.57       ( v1_relat_1 @ C ) ))).
% 0.41/0.57  thf('84', plain,
% 0.41/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.57         ((v1_relat_1 @ X11)
% 0.41/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.41/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.57  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.57      inference('sup-', [status(thm)], ['83', '84'])).
% 0.41/0.57  thf('86', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.41/0.57      inference('demod', [status(thm)], ['78', '81', '82', '85'])).
% 0.41/0.57  thf('87', plain, ($false), inference('demod', [status(thm)], ['56', '86'])).
% 0.41/0.57  
% 0.41/0.57  % SZS output end Refutation
% 0.41/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
