%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BjrwxBamhC

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:05 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 880 expanded)
%              Number of leaves         :   40 ( 277 expanded)
%              Depth                    :   32
%              Number of atoms          : 1359 (9199 expanded)
%              Number of equality atoms :   79 ( 436 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_3 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( ( k7_relset_1 @ X52 @ X53 @ X51 @ X54 )
        = ( k9_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_3 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v4_relat_1 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D_3 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v4_relat_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_3 ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('22',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_3 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( v4_relat_1 @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( v4_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_3 ) )
      | ( v4_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D_3 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D_3 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D_3 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v4_relat_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('49',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( X39
       != ( k2_relat_1 @ X37 ) )
      | ( r2_hidden @ ( sk_D_2 @ X40 @ X37 ) @ ( k1_relat_1 @ X37 ) )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('50',plain,(
    ! [X37: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( r2_hidden @ X40 @ ( k2_relat_1 @ X37 ) )
      | ( r2_hidden @ ( sk_D_2 @ X40 @ X37 ) @ ( k1_relat_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ~ ( r1_tarski @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( sk_D_2 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D_3 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33
        = ( k7_relat_1 @ X33 @ X34 ) )
      | ~ ( v4_relat_1 @ X33 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( sk_D_3
        = ( k7_relat_1 @ sk_D_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) )
      | ( sk_D_3
        = ( k7_relat_1 @ sk_D_3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X31 @ X32 ) )
        = ( k9_relat_1 @ X31 @ X32 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D_3 )
        = ( k9_relat_1 @ sk_D_3 @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D_3 )
        = ( k9_relat_1 @ sk_D_3 @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_3 @ sk_C_2 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_3 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('73',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','73'])).

thf('75',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X37: $i,X39: $i,X41: $i,X42: $i] :
      ( ( X39
       != ( k2_relat_1 @ X37 ) )
      | ( r2_hidden @ X41 @ X39 )
      | ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X37 ) )
      | ( X41
       != ( k1_funct_1 @ X37 @ X42 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('77',plain,(
    ! [X37: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X37 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X42 ) @ ( k2_relat_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_A ) @ ( k2_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('81',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_A ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('83',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D_3 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','73'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('88',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 )
      | ( ( sk_D_2 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) @ sk_D_3 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('93',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 )
      | ( ( sk_D_2 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) @ sk_D_3 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('96',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( X39
       != ( k2_relat_1 @ X37 ) )
      | ( X40
        = ( k1_funct_1 @ X37 @ ( sk_D_2 @ X40 @ X37 ) ) )
      | ~ ( r2_hidden @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('97',plain,(
    ! [X37: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( r2_hidden @ X40 @ ( k2_relat_1 @ X37 ) )
      | ( X40
        = ( k1_funct_1 @ X37 @ ( sk_D_2 @ X40 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_3 ) )
        = ( k1_funct_1 @ sk_D_3 @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('101',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_3 ) )
        = ( k1_funct_1 @ sk_D_3 @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_D_3 ) )
        = ( k1_funct_1 @ sk_D_3 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_D_3 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','107'])).

thf('109',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_D_3 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('111',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_D_3 ) @ ( k2_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( v4_relat_1 @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( v4_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('118',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33
        = ( k7_relat_1 @ X33 @ X34 ) )
      | ~ ( v4_relat_1 @ X33 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( sk_D_3
        = ( k7_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('122',plain,(
    ! [X0: $i] :
      ( sk_D_3
      = ( k7_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X31 @ X32 ) )
        = ( k9_relat_1 @ X31 @ X32 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('124',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X29 @ X30 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) @ X1 ) @ ( k9_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('128',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('129',plain,(
    ! [X0: $i] :
      ( sk_D_3
      = ( k7_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('130',plain,(
    ! [X0: $i] :
      ( sk_D_3
      = ( k7_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('131',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X31 @ X32 ) )
        = ( k9_relat_1 @ X31 @ X32 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D_3 )
        = ( k9_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['13','14'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ sk_D_3 )
      = ( k9_relat_1 @ sk_D_3 @ ( k2_tarski @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D_3 @ X1 ) @ ( k2_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['126','127','128','129','134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['4','108','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BjrwxBamhC
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.24/1.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.24/1.46  % Solved by: fo/fo7.sh
% 1.24/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.24/1.46  % done 2096 iterations in 1.031s
% 1.24/1.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.24/1.46  % SZS output start Refutation
% 1.24/1.46  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.24/1.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.24/1.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.24/1.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.24/1.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.24/1.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.24/1.46  thf(sk_B_type, type, sk_B: $i).
% 1.24/1.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.24/1.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.24/1.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.24/1.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.24/1.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.24/1.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.24/1.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.24/1.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.24/1.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.24/1.46  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.24/1.46  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.24/1.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.24/1.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.24/1.46  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.24/1.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.24/1.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.24/1.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.24/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.24/1.46  thf(t64_funct_2, conjecture,
% 1.24/1.46    (![A:$i,B:$i,C:$i,D:$i]:
% 1.24/1.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.24/1.46         ( m1_subset_1 @
% 1.24/1.46           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.24/1.46       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.24/1.46         ( r1_tarski @
% 1.24/1.46           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.24/1.46           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 1.24/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.24/1.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.24/1.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 1.24/1.46            ( m1_subset_1 @
% 1.24/1.46              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.24/1.46          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.24/1.46            ( r1_tarski @
% 1.24/1.46              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 1.24/1.46              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 1.24/1.46    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 1.24/1.46  thf('0', plain,
% 1.24/1.46      (~ (r1_tarski @ 
% 1.24/1.46          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_3 @ sk_C_2) @ 
% 1.24/1.46          (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A)))),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('1', plain,
% 1.24/1.46      ((m1_subset_1 @ sk_D_3 @ 
% 1.24/1.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf(redefinition_k7_relset_1, axiom,
% 1.24/1.46    (![A:$i,B:$i,C:$i,D:$i]:
% 1.24/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.24/1.46       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.24/1.46  thf('2', plain,
% 1.24/1.46      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.24/1.46         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.24/1.46          | ((k7_relset_1 @ X52 @ X53 @ X51 @ X54) = (k9_relat_1 @ X51 @ X54)))),
% 1.24/1.46      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.24/1.46  thf('3', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_3 @ X0)
% 1.24/1.46           = (k9_relat_1 @ sk_D_3 @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['1', '2'])).
% 1.24/1.46  thf('4', plain,
% 1.24/1.46      (~ (r1_tarski @ (k9_relat_1 @ sk_D_3 @ sk_C_2) @ 
% 1.24/1.46          (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['0', '3'])).
% 1.24/1.46  thf(d3_tarski, axiom,
% 1.24/1.46    (![A:$i,B:$i]:
% 1.24/1.46     ( ( r1_tarski @ A @ B ) <=>
% 1.24/1.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.24/1.46  thf('5', plain,
% 1.24/1.46      (![X1 : $i, X3 : $i]:
% 1.24/1.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf('6', plain,
% 1.24/1.46      ((m1_subset_1 @ sk_D_3 @ 
% 1.24/1.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf(cc2_relset_1, axiom,
% 1.24/1.46    (![A:$i,B:$i,C:$i]:
% 1.24/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.24/1.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.24/1.46  thf('7', plain,
% 1.24/1.46      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.24/1.46         ((v4_relat_1 @ X48 @ X49)
% 1.24/1.46          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 1.24/1.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.24/1.46  thf('8', plain, ((v4_relat_1 @ sk_D_3 @ (k1_tarski @ sk_A))),
% 1.24/1.46      inference('sup-', [status(thm)], ['6', '7'])).
% 1.24/1.46  thf(d18_relat_1, axiom,
% 1.24/1.46    (![A:$i,B:$i]:
% 1.24/1.46     ( ( v1_relat_1 @ B ) =>
% 1.24/1.46       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.24/1.46  thf('9', plain,
% 1.24/1.46      (![X25 : $i, X26 : $i]:
% 1.24/1.46         (~ (v4_relat_1 @ X25 @ X26)
% 1.24/1.46          | (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 1.24/1.46          | ~ (v1_relat_1 @ X25))),
% 1.24/1.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.24/1.46  thf('10', plain,
% 1.24/1.46      ((~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46        | (r1_tarski @ (k1_relat_1 @ sk_D_3) @ (k1_tarski @ sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['8', '9'])).
% 1.24/1.46  thf('11', plain,
% 1.24/1.46      ((m1_subset_1 @ sk_D_3 @ 
% 1.24/1.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf(cc2_relat_1, axiom,
% 1.24/1.46    (![A:$i]:
% 1.24/1.46     ( ( v1_relat_1 @ A ) =>
% 1.24/1.46       ( ![B:$i]:
% 1.24/1.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.24/1.46  thf('12', plain,
% 1.24/1.46      (![X23 : $i, X24 : $i]:
% 1.24/1.46         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.24/1.46          | (v1_relat_1 @ X23)
% 1.24/1.46          | ~ (v1_relat_1 @ X24))),
% 1.24/1.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.24/1.46  thf('13', plain,
% 1.24/1.46      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 1.24/1.46        | (v1_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('sup-', [status(thm)], ['11', '12'])).
% 1.24/1.46  thf(fc6_relat_1, axiom,
% 1.24/1.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.24/1.46  thf('14', plain,
% 1.24/1.46      (![X27 : $i, X28 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X27 @ X28))),
% 1.24/1.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.24/1.46  thf('15', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_3) @ (k1_tarski @ sk_A))),
% 1.24/1.46      inference('demod', [status(thm)], ['10', '15'])).
% 1.24/1.46  thf('17', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.24/1.46         (~ (r2_hidden @ X0 @ X1)
% 1.24/1.46          | (r2_hidden @ X0 @ X2)
% 1.24/1.46          | ~ (r1_tarski @ X1 @ X2))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf('18', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.24/1.46          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['16', '17'])).
% 1.24/1.46  thf('19', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_D_3)) @ 
% 1.24/1.46             (k1_tarski @ sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['5', '18'])).
% 1.24/1.46  thf(t69_enumset1, axiom,
% 1.24/1.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.24/1.46  thf('20', plain,
% 1.24/1.46      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 1.24/1.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.24/1.46  thf(d2_tarski, axiom,
% 1.24/1.46    (![A:$i,B:$i,C:$i]:
% 1.24/1.46     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.24/1.46       ( ![D:$i]:
% 1.24/1.46         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.24/1.46  thf('21', plain,
% 1.24/1.46      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.24/1.46         (~ (r2_hidden @ X12 @ X10)
% 1.24/1.46          | ((X12) = (X11))
% 1.24/1.46          | ((X12) = (X8))
% 1.24/1.46          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 1.24/1.46      inference('cnf', [status(esa)], [d2_tarski])).
% 1.24/1.46  thf('22', plain,
% 1.24/1.46      (![X8 : $i, X11 : $i, X12 : $i]:
% 1.24/1.46         (((X12) = (X8))
% 1.24/1.46          | ((X12) = (X11))
% 1.24/1.46          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 1.24/1.46      inference('simplify', [status(thm)], ['21'])).
% 1.24/1.46  thf('23', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['20', '22'])).
% 1.24/1.46  thf('24', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.24/1.46      inference('simplify', [status(thm)], ['23'])).
% 1.24/1.46  thf('25', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_3)) = (sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['19', '24'])).
% 1.24/1.46  thf('26', plain,
% 1.24/1.46      (![X1 : $i, X3 : $i]:
% 1.24/1.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf('27', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | (r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | (r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0))),
% 1.24/1.46      inference('sup+', [status(thm)], ['25', '26'])).
% 1.24/1.46  thf('28', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('simplify', [status(thm)], ['27'])).
% 1.24/1.46  thf('29', plain,
% 1.24/1.46      (![X25 : $i, X26 : $i]:
% 1.24/1.46         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 1.24/1.46          | (v4_relat_1 @ X25 @ X26)
% 1.24/1.46          | ~ (v1_relat_1 @ X25))),
% 1.24/1.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.24/1.46  thf('30', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | ~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | (v4_relat_1 @ sk_D_3 @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['28', '29'])).
% 1.24/1.46  thf('31', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('32', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | (v4_relat_1 @ sk_D_3 @ X0))),
% 1.24/1.46      inference('demod', [status(thm)], ['30', '31'])).
% 1.24/1.46  thf('33', plain,
% 1.24/1.46      (![X1 : $i, X3 : $i]:
% 1.24/1.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf('34', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.24/1.46      inference('simplify', [status(thm)], ['23'])).
% 1.24/1.46  thf('35', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.24/1.46          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['33', '34'])).
% 1.24/1.46  thf('36', plain,
% 1.24/1.46      (![X1 : $i, X3 : $i]:
% 1.24/1.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf('37', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         (~ (r2_hidden @ X0 @ X1)
% 1.24/1.46          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.24/1.46          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.24/1.46      inference('sup-', [status(thm)], ['35', '36'])).
% 1.24/1.46  thf('38', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.24/1.46      inference('simplify', [status(thm)], ['37'])).
% 1.24/1.46  thf('39', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((v4_relat_1 @ sk_D_3 @ X0)
% 1.24/1.46          | (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['32', '38'])).
% 1.24/1.46  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_3) @ (k1_tarski @ sk_A))),
% 1.24/1.46      inference('demod', [status(thm)], ['10', '15'])).
% 1.24/1.46  thf(d10_xboole_0, axiom,
% 1.24/1.46    (![A:$i,B:$i]:
% 1.24/1.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.24/1.46  thf('41', plain,
% 1.24/1.46      (![X4 : $i, X6 : $i]:
% 1.24/1.46         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.24/1.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.24/1.46  thf('42', plain,
% 1.24/1.46      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D_3))
% 1.24/1.46        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['40', '41'])).
% 1.24/1.46  thf('43', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((v4_relat_1 @ sk_D_3 @ X0)
% 1.24/1.46          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['39', '42'])).
% 1.24/1.46  thf('44', plain,
% 1.24/1.46      (![X25 : $i, X26 : $i]:
% 1.24/1.46         (~ (v4_relat_1 @ X25 @ X26)
% 1.24/1.46          | (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 1.24/1.46          | ~ (v1_relat_1 @ X25))),
% 1.24/1.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.24/1.46  thf('45', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | ~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | (r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['43', '44'])).
% 1.24/1.46  thf('46', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('47', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | (r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0))),
% 1.24/1.46      inference('demod', [status(thm)], ['45', '46'])).
% 1.24/1.46  thf('48', plain,
% 1.24/1.46      (![X1 : $i, X3 : $i]:
% 1.24/1.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf(d5_funct_1, axiom,
% 1.24/1.46    (![A:$i]:
% 1.24/1.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.24/1.46       ( ![B:$i]:
% 1.24/1.46         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.24/1.46           ( ![C:$i]:
% 1.24/1.46             ( ( r2_hidden @ C @ B ) <=>
% 1.24/1.46               ( ?[D:$i]:
% 1.24/1.46                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.24/1.46                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.24/1.46  thf('49', plain,
% 1.24/1.46      (![X37 : $i, X39 : $i, X40 : $i]:
% 1.24/1.46         (((X39) != (k2_relat_1 @ X37))
% 1.24/1.46          | (r2_hidden @ (sk_D_2 @ X40 @ X37) @ (k1_relat_1 @ X37))
% 1.24/1.46          | ~ (r2_hidden @ X40 @ X39)
% 1.24/1.46          | ~ (v1_funct_1 @ X37)
% 1.24/1.46          | ~ (v1_relat_1 @ X37))),
% 1.24/1.46      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.24/1.46  thf('50', plain,
% 1.24/1.46      (![X37 : $i, X40 : $i]:
% 1.24/1.46         (~ (v1_relat_1 @ X37)
% 1.24/1.46          | ~ (v1_funct_1 @ X37)
% 1.24/1.46          | ~ (r2_hidden @ X40 @ (k2_relat_1 @ X37))
% 1.24/1.46          | (r2_hidden @ (sk_D_2 @ X40 @ X37) @ (k1_relat_1 @ X37)))),
% 1.24/1.46      inference('simplify', [status(thm)], ['49'])).
% 1.24/1.46  thf('51', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.24/1.46          | (r2_hidden @ (sk_D_2 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.24/1.46             (k1_relat_1 @ X0))
% 1.24/1.46          | ~ (v1_funct_1 @ X0)
% 1.24/1.46          | ~ (v1_relat_1 @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['48', '50'])).
% 1.24/1.46  thf(t7_ordinal1, axiom,
% 1.24/1.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.24/1.46  thf('52', plain,
% 1.24/1.46      (![X46 : $i, X47 : $i]:
% 1.24/1.46         (~ (r2_hidden @ X46 @ X47) | ~ (r1_tarski @ X47 @ X46))),
% 1.24/1.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.24/1.46  thf('53', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         (~ (v1_relat_1 @ X0)
% 1.24/1.46          | ~ (v1_funct_1 @ X0)
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.24/1.46          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.24/1.46               (sk_D_2 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['51', '52'])).
% 1.24/1.46  thf('54', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | ~ (v1_funct_1 @ sk_D_3)
% 1.24/1.46          | ~ (v1_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('sup-', [status(thm)], ['47', '53'])).
% 1.24/1.46  thf('55', plain, ((v1_funct_1 @ sk_D_3)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('56', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('57', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0))),
% 1.24/1.46      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.24/1.46  thf('58', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((v4_relat_1 @ sk_D_3 @ X0)
% 1.24/1.46          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['39', '42'])).
% 1.24/1.46  thf(t209_relat_1, axiom,
% 1.24/1.46    (![A:$i,B:$i]:
% 1.24/1.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.24/1.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.24/1.46  thf('59', plain,
% 1.24/1.46      (![X33 : $i, X34 : $i]:
% 1.24/1.46         (((X33) = (k7_relat_1 @ X33 @ X34))
% 1.24/1.46          | ~ (v4_relat_1 @ X33 @ X34)
% 1.24/1.46          | ~ (v1_relat_1 @ X33))),
% 1.24/1.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.24/1.46  thf('60', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | ~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | ((sk_D_3) = (k7_relat_1 @ sk_D_3 @ X0)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['58', '59'])).
% 1.24/1.46  thf('61', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('62', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | ((sk_D_3) = (k7_relat_1 @ sk_D_3 @ X0)))),
% 1.24/1.46      inference('demod', [status(thm)], ['60', '61'])).
% 1.24/1.46  thf(t148_relat_1, axiom,
% 1.24/1.46    (![A:$i,B:$i]:
% 1.24/1.46     ( ( v1_relat_1 @ B ) =>
% 1.24/1.46       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.24/1.46  thf('63', plain,
% 1.24/1.46      (![X31 : $i, X32 : $i]:
% 1.24/1.46         (((k2_relat_1 @ (k7_relat_1 @ X31 @ X32)) = (k9_relat_1 @ X31 @ X32))
% 1.24/1.46          | ~ (v1_relat_1 @ X31))),
% 1.24/1.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.24/1.46  thf('64', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k2_relat_1 @ sk_D_3) = (k9_relat_1 @ sk_D_3 @ X0))
% 1.24/1.46          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))
% 1.24/1.46          | ~ (v1_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('sup+', [status(thm)], ['62', '63'])).
% 1.24/1.46  thf('65', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('66', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k2_relat_1 @ sk_D_3) = (k9_relat_1 @ sk_D_3 @ X0))
% 1.24/1.46          | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('demod', [status(thm)], ['64', '65'])).
% 1.24/1.46  thf('67', plain,
% 1.24/1.46      (~ (r1_tarski @ (k9_relat_1 @ sk_D_3 @ sk_C_2) @ 
% 1.24/1.46          (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['0', '3'])).
% 1.24/1.46  thf('68', plain,
% 1.24/1.46      ((~ (r1_tarski @ (k2_relat_1 @ sk_D_3) @ 
% 1.24/1.46           (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A)))
% 1.24/1.46        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['66', '67'])).
% 1.24/1.46  thf('69', plain,
% 1.24/1.46      ((((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))
% 1.24/1.46        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['57', '68'])).
% 1.24/1.46  thf('70', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('simplify', [status(thm)], ['69'])).
% 1.24/1.46  thf('71', plain,
% 1.24/1.46      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 1.24/1.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.24/1.46  thf('72', plain,
% 1.24/1.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.24/1.46         (((X9) != (X8))
% 1.24/1.46          | (r2_hidden @ X9 @ X10)
% 1.24/1.46          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 1.24/1.46      inference('cnf', [status(esa)], [d2_tarski])).
% 1.24/1.46  thf('73', plain,
% 1.24/1.46      (![X8 : $i, X11 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X11 @ X8))),
% 1.24/1.46      inference('simplify', [status(thm)], ['72'])).
% 1.24/1.46  thf('74', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.24/1.46      inference('sup+', [status(thm)], ['71', '73'])).
% 1.24/1.46  thf('75', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('sup+', [status(thm)], ['70', '74'])).
% 1.24/1.46  thf('76', plain,
% 1.24/1.46      (![X37 : $i, X39 : $i, X41 : $i, X42 : $i]:
% 1.24/1.46         (((X39) != (k2_relat_1 @ X37))
% 1.24/1.46          | (r2_hidden @ X41 @ X39)
% 1.24/1.46          | ~ (r2_hidden @ X42 @ (k1_relat_1 @ X37))
% 1.24/1.46          | ((X41) != (k1_funct_1 @ X37 @ X42))
% 1.24/1.46          | ~ (v1_funct_1 @ X37)
% 1.24/1.46          | ~ (v1_relat_1 @ X37))),
% 1.24/1.46      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.24/1.46  thf('77', plain,
% 1.24/1.46      (![X37 : $i, X42 : $i]:
% 1.24/1.46         (~ (v1_relat_1 @ X37)
% 1.24/1.46          | ~ (v1_funct_1 @ X37)
% 1.24/1.46          | ~ (r2_hidden @ X42 @ (k1_relat_1 @ X37))
% 1.24/1.46          | (r2_hidden @ (k1_funct_1 @ X37 @ X42) @ (k2_relat_1 @ X37)))),
% 1.24/1.46      inference('simplify', [status(thm)], ['76'])).
% 1.24/1.46  thf('78', plain,
% 1.24/1.46      (((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_A) @ (k2_relat_1 @ sk_D_3))
% 1.24/1.46        | ~ (v1_funct_1 @ sk_D_3)
% 1.24/1.46        | ~ (v1_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('sup-', [status(thm)], ['75', '77'])).
% 1.24/1.46  thf('79', plain, ((v1_funct_1 @ sk_D_3)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('80', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('81', plain,
% 1.24/1.46      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_A) @ (k2_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.24/1.46  thf('82', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.24/1.46      inference('simplify', [status(thm)], ['37'])).
% 1.24/1.46  thf('83', plain,
% 1.24/1.46      ((r1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A)) @ 
% 1.24/1.46        (k2_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('sup-', [status(thm)], ['81', '82'])).
% 1.24/1.46  thf('84', plain,
% 1.24/1.46      (![X4 : $i, X6 : $i]:
% 1.24/1.46         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.24/1.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.24/1.46  thf('85', plain,
% 1.24/1.46      ((~ (r1_tarski @ (k2_relat_1 @ sk_D_3) @ 
% 1.24/1.46           (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A)))
% 1.24/1.46        | ((k2_relat_1 @ sk_D_3) = (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A))))),
% 1.24/1.46      inference('sup-', [status(thm)], ['83', '84'])).
% 1.24/1.46  thf('86', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.24/1.46      inference('sup+', [status(thm)], ['71', '73'])).
% 1.24/1.46  thf('87', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.24/1.46          | (r2_hidden @ (sk_D_2 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.24/1.46             (k1_relat_1 @ X0))
% 1.24/1.46          | ~ (v1_funct_1 @ X0)
% 1.24/1.46          | ~ (v1_relat_1 @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['48', '50'])).
% 1.24/1.46  thf('88', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('simplify', [status(thm)], ['69'])).
% 1.24/1.46  thf('89', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.24/1.46      inference('simplify', [status(thm)], ['23'])).
% 1.24/1.46  thf('90', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_3)) | ((X0) = (sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['88', '89'])).
% 1.24/1.46  thf('91', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | ~ (v1_funct_1 @ sk_D_3)
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | ((sk_D_2 @ (sk_C @ X0 @ (k2_relat_1 @ sk_D_3)) @ sk_D_3) = (sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['87', '90'])).
% 1.24/1.46  thf('92', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('93', plain, ((v1_funct_1 @ sk_D_3)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('94', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | ((sk_D_2 @ (sk_C @ X0 @ (k2_relat_1 @ sk_D_3)) @ sk_D_3) = (sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.24/1.46  thf('95', plain,
% 1.24/1.46      (![X1 : $i, X3 : $i]:
% 1.24/1.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf('96', plain,
% 1.24/1.46      (![X37 : $i, X39 : $i, X40 : $i]:
% 1.24/1.46         (((X39) != (k2_relat_1 @ X37))
% 1.24/1.46          | ((X40) = (k1_funct_1 @ X37 @ (sk_D_2 @ X40 @ X37)))
% 1.24/1.46          | ~ (r2_hidden @ X40 @ X39)
% 1.24/1.46          | ~ (v1_funct_1 @ X37)
% 1.24/1.46          | ~ (v1_relat_1 @ X37))),
% 1.24/1.46      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.24/1.46  thf('97', plain,
% 1.24/1.46      (![X37 : $i, X40 : $i]:
% 1.24/1.46         (~ (v1_relat_1 @ X37)
% 1.24/1.46          | ~ (v1_funct_1 @ X37)
% 1.24/1.46          | ~ (r2_hidden @ X40 @ (k2_relat_1 @ X37))
% 1.24/1.46          | ((X40) = (k1_funct_1 @ X37 @ (sk_D_2 @ X40 @ X37))))),
% 1.24/1.46      inference('simplify', [status(thm)], ['96'])).
% 1.24/1.46  thf('98', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.24/1.46          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 1.24/1.46              = (k1_funct_1 @ X0 @ 
% 1.24/1.46                 (sk_D_2 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 1.24/1.46          | ~ (v1_funct_1 @ X0)
% 1.24/1.46          | ~ (v1_relat_1 @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['95', '97'])).
% 1.24/1.46  thf('99', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((sk_C @ X0 @ (k2_relat_1 @ sk_D_3)) = (k1_funct_1 @ sk_D_3 @ sk_A))
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | ~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | ~ (v1_funct_1 @ sk_D_3)
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0))),
% 1.24/1.46      inference('sup+', [status(thm)], ['94', '98'])).
% 1.24/1.46  thf('100', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('101', plain, ((v1_funct_1 @ sk_D_3)),
% 1.24/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.24/1.46  thf('102', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((sk_C @ X0 @ (k2_relat_1 @ sk_D_3)) = (k1_funct_1 @ sk_D_3 @ sk_A))
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0))),
% 1.24/1.46      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.24/1.46  thf('103', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | ((sk_C @ X0 @ (k2_relat_1 @ sk_D_3)) = (k1_funct_1 @ sk_D_3 @ sk_A)))),
% 1.24/1.46      inference('simplify', [status(thm)], ['102'])).
% 1.24/1.46  thf('104', plain,
% 1.24/1.46      (![X1 : $i, X3 : $i]:
% 1.24/1.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf('105', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_A) @ X0)
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['103', '104'])).
% 1.24/1.46  thf('106', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | ~ (r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_A) @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['105'])).
% 1.24/1.46  thf('107', plain,
% 1.24/1.46      ((r1_tarski @ (k2_relat_1 @ sk_D_3) @ 
% 1.24/1.46        (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['86', '106'])).
% 1.24/1.46  thf('108', plain,
% 1.24/1.46      (((k2_relat_1 @ sk_D_3) = (k1_tarski @ (k1_funct_1 @ sk_D_3 @ sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['85', '107'])).
% 1.24/1.46  thf('109', plain,
% 1.24/1.46      (![X8 : $i, X11 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X11 @ X8))),
% 1.24/1.46      inference('simplify', [status(thm)], ['72'])).
% 1.24/1.46  thf('110', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | ((sk_C @ X0 @ (k1_relat_1 @ sk_D_3)) = (sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['19', '24'])).
% 1.24/1.46  thf('111', plain,
% 1.24/1.46      (![X1 : $i, X3 : $i]:
% 1.24/1.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.24/1.46      inference('cnf', [status(esa)], [d3_tarski])).
% 1.24/1.46  thf('112', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (r2_hidden @ sk_A @ X0)
% 1.24/1.46          | (r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0)
% 1.24/1.46          | (r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0))),
% 1.24/1.46      inference('sup-', [status(thm)], ['110', '111'])).
% 1.24/1.46  thf('113', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((r1_tarski @ (k1_relat_1 @ sk_D_3) @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 1.24/1.46      inference('simplify', [status(thm)], ['112'])).
% 1.24/1.46  thf('114', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (r1_tarski @ (k1_relat_1 @ sk_D_3) @ (k2_tarski @ X0 @ sk_A))),
% 1.24/1.46      inference('sup-', [status(thm)], ['109', '113'])).
% 1.24/1.46  thf('115', plain,
% 1.24/1.46      (![X25 : $i, X26 : $i]:
% 1.24/1.46         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 1.24/1.46          | (v4_relat_1 @ X25 @ X26)
% 1.24/1.46          | ~ (v1_relat_1 @ X25))),
% 1.24/1.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.24/1.46  thf('116', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | (v4_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A)))),
% 1.24/1.46      inference('sup-', [status(thm)], ['114', '115'])).
% 1.24/1.46  thf('117', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('118', plain,
% 1.24/1.46      (![X0 : $i]: (v4_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A))),
% 1.24/1.46      inference('demod', [status(thm)], ['116', '117'])).
% 1.24/1.46  thf('119', plain,
% 1.24/1.46      (![X33 : $i, X34 : $i]:
% 1.24/1.46         (((X33) = (k7_relat_1 @ X33 @ X34))
% 1.24/1.46          | ~ (v4_relat_1 @ X33 @ X34)
% 1.24/1.46          | ~ (v1_relat_1 @ X33))),
% 1.24/1.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.24/1.46  thf('120', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | ((sk_D_3) = (k7_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A))))),
% 1.24/1.46      inference('sup-', [status(thm)], ['118', '119'])).
% 1.24/1.46  thf('121', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('122', plain,
% 1.24/1.46      (![X0 : $i]: ((sk_D_3) = (k7_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['120', '121'])).
% 1.24/1.46  thf('123', plain,
% 1.24/1.46      (![X31 : $i, X32 : $i]:
% 1.24/1.46         (((k2_relat_1 @ (k7_relat_1 @ X31 @ X32)) = (k9_relat_1 @ X31 @ X32))
% 1.24/1.46          | ~ (v1_relat_1 @ X31))),
% 1.24/1.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.24/1.46  thf(t144_relat_1, axiom,
% 1.24/1.46    (![A:$i,B:$i]:
% 1.24/1.46     ( ( v1_relat_1 @ B ) =>
% 1.24/1.46       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 1.24/1.46  thf('124', plain,
% 1.24/1.46      (![X29 : $i, X30 : $i]:
% 1.24/1.46         ((r1_tarski @ (k9_relat_1 @ X29 @ X30) @ (k2_relat_1 @ X29))
% 1.24/1.46          | ~ (v1_relat_1 @ X29))),
% 1.24/1.46      inference('cnf', [status(esa)], [t144_relat_1])).
% 1.24/1.46  thf('125', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.24/1.46         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 1.24/1.46           (k9_relat_1 @ X1 @ X0))
% 1.24/1.46          | ~ (v1_relat_1 @ X1)
% 1.24/1.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.24/1.46      inference('sup+', [status(thm)], ['123', '124'])).
% 1.24/1.46  thf('126', plain,
% 1.24/1.46      (![X0 : $i, X1 : $i]:
% 1.24/1.46         (~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | ~ (v1_relat_1 @ sk_D_3)
% 1.24/1.46          | (r1_tarski @ 
% 1.24/1.46             (k9_relat_1 @ (k7_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A)) @ X1) @ 
% 1.24/1.46             (k9_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A))))),
% 1.24/1.46      inference('sup-', [status(thm)], ['122', '125'])).
% 1.24/1.46  thf('127', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('128', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('129', plain,
% 1.24/1.46      (![X0 : $i]: ((sk_D_3) = (k7_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['120', '121'])).
% 1.24/1.46  thf('130', plain,
% 1.24/1.46      (![X0 : $i]: ((sk_D_3) = (k7_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['120', '121'])).
% 1.24/1.46  thf('131', plain,
% 1.24/1.46      (![X31 : $i, X32 : $i]:
% 1.24/1.46         (((k2_relat_1 @ (k7_relat_1 @ X31 @ X32)) = (k9_relat_1 @ X31 @ X32))
% 1.24/1.46          | ~ (v1_relat_1 @ X31))),
% 1.24/1.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.24/1.46  thf('132', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         (((k2_relat_1 @ sk_D_3)
% 1.24/1.46            = (k9_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A)))
% 1.24/1.46          | ~ (v1_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('sup+', [status(thm)], ['130', '131'])).
% 1.24/1.46  thf('133', plain, ((v1_relat_1 @ sk_D_3)),
% 1.24/1.46      inference('demod', [status(thm)], ['13', '14'])).
% 1.24/1.46  thf('134', plain,
% 1.24/1.46      (![X0 : $i]:
% 1.24/1.46         ((k2_relat_1 @ sk_D_3)
% 1.24/1.46           = (k9_relat_1 @ sk_D_3 @ (k2_tarski @ X0 @ sk_A)))),
% 1.24/1.46      inference('demod', [status(thm)], ['132', '133'])).
% 1.24/1.46  thf('135', plain,
% 1.24/1.46      (![X1 : $i]:
% 1.24/1.46         (r1_tarski @ (k9_relat_1 @ sk_D_3 @ X1) @ (k2_relat_1 @ sk_D_3))),
% 1.24/1.46      inference('demod', [status(thm)], ['126', '127', '128', '129', '134'])).
% 1.24/1.46  thf('136', plain, ($false),
% 1.24/1.46      inference('demod', [status(thm)], ['4', '108', '135'])).
% 1.24/1.46  
% 1.24/1.46  % SZS output end Refutation
% 1.24/1.46  
% 1.29/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
