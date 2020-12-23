%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MLusBt5JGa

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:41 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 315 expanded)
%              Number of leaves         :   36 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :  932 (2580 expanded)
%              Number of equality atoms :   61 ( 137 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','30'])).

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

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('36',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ~ ( v1_funct_2 @ sk_A @ k1_xboole_0 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('51',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X21 )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('64',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['51','62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ sk_A @ k1_xboole_0 @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['48','64'])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('70',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('74',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('82',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['51','62','63'])).

thf('83',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('88',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('93',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['67','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MLusBt5JGa
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.28/1.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.28/1.47  % Solved by: fo/fo7.sh
% 1.28/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.47  % done 1312 iterations in 1.015s
% 1.28/1.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.28/1.47  % SZS output start Refutation
% 1.28/1.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.28/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.28/1.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.28/1.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.28/1.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.28/1.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.28/1.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.28/1.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.28/1.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.28/1.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.28/1.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.28/1.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.28/1.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.28/1.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.28/1.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.28/1.47  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.28/1.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.28/1.47  thf(t7_xboole_0, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.28/1.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.28/1.47  thf('0', plain,
% 1.28/1.47      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 1.28/1.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.28/1.47  thf(d1_xboole_0, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.28/1.47  thf('1', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.28/1.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.28/1.47  thf('2', plain,
% 1.28/1.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.28/1.47      inference('sup-', [status(thm)], ['0', '1'])).
% 1.28/1.47  thf(t113_zfmisc_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.28/1.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.28/1.47  thf('3', plain,
% 1.28/1.47      (![X5 : $i, X6 : $i]:
% 1.28/1.47         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.28/1.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.28/1.47  thf('4', plain,
% 1.28/1.47      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.28/1.47      inference('simplify', [status(thm)], ['3'])).
% 1.28/1.47  thf(dt_k2_subset_1, axiom,
% 1.28/1.47    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.28/1.47  thf('5', plain,
% 1.28/1.47      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 1.28/1.47      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.28/1.47  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.28/1.47  thf('6', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 1.28/1.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.28/1.47  thf('7', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 1.28/1.47      inference('demod', [status(thm)], ['5', '6'])).
% 1.28/1.47  thf(redefinition_k1_relset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.28/1.47  thf('8', plain,
% 1.28/1.47      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.28/1.47         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.28/1.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.28/1.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.28/1.47  thf('9', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.28/1.47           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['7', '8'])).
% 1.28/1.47  thf('10', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.28/1.47           = (k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 1.28/1.47      inference('sup+', [status(thm)], ['4', '9'])).
% 1.28/1.47  thf('11', plain,
% 1.28/1.47      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.28/1.47      inference('simplify', [status(thm)], ['3'])).
% 1.28/1.47  thf('12', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.28/1.47           = (k1_relat_1 @ k1_xboole_0))),
% 1.28/1.47      inference('demod', [status(thm)], ['10', '11'])).
% 1.28/1.47  thf('13', plain,
% 1.28/1.47      (![X5 : $i, X6 : $i]:
% 1.28/1.47         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.28/1.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.28/1.47  thf('14', plain,
% 1.28/1.47      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.47      inference('simplify', [status(thm)], ['13'])).
% 1.28/1.47  thf('15', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]:
% 1.28/1.47         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.28/1.47           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['7', '8'])).
% 1.28/1.47  thf('16', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 1.28/1.47           = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 1.28/1.47      inference('sup+', [status(thm)], ['14', '15'])).
% 1.28/1.47  thf('17', plain,
% 1.28/1.47      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.47      inference('simplify', [status(thm)], ['13'])).
% 1.28/1.47  thf('18', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 1.28/1.47           = (k1_relat_1 @ k1_xboole_0))),
% 1.28/1.47      inference('demod', [status(thm)], ['16', '17'])).
% 1.28/1.48  thf(fc10_relat_1, axiom,
% 1.28/1.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 1.28/1.48  thf('19', plain,
% 1.28/1.48      (![X12 : $i]:
% 1.28/1.48         ((v1_xboole_0 @ (k1_relat_1 @ X12)) | ~ (v1_xboole_0 @ X12))),
% 1.28/1.48      inference('cnf', [status(esa)], [fc10_relat_1])).
% 1.28/1.48  thf('20', plain,
% 1.28/1.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['0', '1'])).
% 1.28/1.48  thf('21', plain,
% 1.28/1.48      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.28/1.48      inference('sup-', [status(thm)], ['19', '20'])).
% 1.28/1.48  thf('22', plain,
% 1.28/1.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['0', '1'])).
% 1.28/1.48  thf('23', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 1.28/1.48           = (k1_relat_1 @ k1_xboole_0))),
% 1.28/1.48      inference('demod', [status(thm)], ['16', '17'])).
% 1.28/1.48  thf('24', plain,
% 1.28/1.48      (![X0 : $i, X1 : $i]:
% 1.28/1.48         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 1.28/1.48          | ~ (v1_xboole_0 @ X0))),
% 1.28/1.48      inference('sup+', [status(thm)], ['22', '23'])).
% 1.28/1.48  thf('25', plain,
% 1.28/1.48      (![X0 : $i, X1 : $i]:
% 1.28/1.48         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.28/1.48          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.28/1.48          | ~ (v1_xboole_0 @ X0))),
% 1.28/1.48      inference('sup+', [status(thm)], ['21', '24'])).
% 1.28/1.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.28/1.48  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.28/1.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.28/1.48  thf('27', plain,
% 1.28/1.48      (![X0 : $i, X1 : $i]:
% 1.28/1.48         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.28/1.48          | ~ (v1_xboole_0 @ X0))),
% 1.28/1.48      inference('demod', [status(thm)], ['25', '26'])).
% 1.28/1.48  thf('28', plain,
% 1.28/1.48      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.28/1.48        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.28/1.48      inference('sup+', [status(thm)], ['18', '27'])).
% 1.28/1.48  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.28/1.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.28/1.48  thf('30', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.48      inference('demod', [status(thm)], ['28', '29'])).
% 1.28/1.48  thf('31', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.48      inference('demod', [status(thm)], ['12', '30'])).
% 1.28/1.48  thf(d1_funct_2, axiom,
% 1.28/1.48    (![A:$i,B:$i,C:$i]:
% 1.28/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.28/1.48           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.28/1.48             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.28/1.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.28/1.48           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.28/1.48             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.28/1.48  thf(zf_stmt_0, axiom,
% 1.28/1.48    (![C:$i,B:$i,A:$i]:
% 1.28/1.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.28/1.48       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.28/1.48  thf('32', plain,
% 1.28/1.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.28/1.48         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 1.28/1.48          | (v1_funct_2 @ X26 @ X24 @ X25)
% 1.28/1.48          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.48  thf('33', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         (((k1_xboole_0) != (k1_xboole_0))
% 1.28/1.48          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.28/1.48          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['31', '32'])).
% 1.28/1.48  thf('34', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.28/1.48          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.28/1.48      inference('simplify', [status(thm)], ['33'])).
% 1.28/1.48  thf('35', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 1.28/1.48      inference('demod', [status(thm)], ['5', '6'])).
% 1.28/1.48  thf('36', plain,
% 1.28/1.48      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.28/1.48      inference('simplify', [status(thm)], ['3'])).
% 1.28/1.48  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.28/1.48  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $o).
% 1.28/1.48  thf(zf_stmt_3, axiom,
% 1.28/1.48    (![B:$i,A:$i]:
% 1.28/1.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.28/1.48       ( zip_tseitin_0 @ B @ A ) ))).
% 1.28/1.48  thf(zf_stmt_4, axiom,
% 1.28/1.48    (![A:$i,B:$i,C:$i]:
% 1.28/1.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.48       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.28/1.48         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.28/1.48           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.28/1.48             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.28/1.48  thf('37', plain,
% 1.28/1.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.28/1.48         (~ (zip_tseitin_0 @ X27 @ X28)
% 1.28/1.48          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 1.28/1.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.28/1.48  thf('38', plain,
% 1.28/1.48      (![X0 : $i, X1 : $i]:
% 1.28/1.48         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.28/1.48          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 1.28/1.48          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['36', '37'])).
% 1.28/1.48  thf('39', plain,
% 1.28/1.48      (![X22 : $i, X23 : $i]:
% 1.28/1.48         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.28/1.48  thf('40', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 1.28/1.48      inference('simplify', [status(thm)], ['39'])).
% 1.28/1.48  thf('41', plain,
% 1.28/1.48      (![X0 : $i, X1 : $i]:
% 1.28/1.48         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.28/1.48          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.28/1.48      inference('demod', [status(thm)], ['38', '40'])).
% 1.28/1.48  thf('42', plain,
% 1.28/1.48      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.28/1.48      inference('sup-', [status(thm)], ['35', '41'])).
% 1.28/1.48  thf('43', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.28/1.48      inference('demod', [status(thm)], ['34', '42'])).
% 1.28/1.48  thf('44', plain,
% 1.28/1.48      (![X0 : $i, X1 : $i]:
% 1.28/1.48         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.28/1.48      inference('sup+', [status(thm)], ['2', '43'])).
% 1.28/1.48  thf('45', plain,
% 1.28/1.48      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.28/1.48      inference('sup-', [status(thm)], ['19', '20'])).
% 1.28/1.48  thf(t3_funct_2, conjecture,
% 1.28/1.48    (![A:$i]:
% 1.28/1.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.28/1.48       ( ( v1_funct_1 @ A ) & 
% 1.28/1.48         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.28/1.48         ( m1_subset_1 @
% 1.28/1.48           A @ 
% 1.28/1.48           ( k1_zfmisc_1 @
% 1.28/1.48             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.28/1.48  thf(zf_stmt_5, negated_conjecture,
% 1.28/1.48    (~( ![A:$i]:
% 1.28/1.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.28/1.48          ( ( v1_funct_1 @ A ) & 
% 1.28/1.48            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.28/1.48            ( m1_subset_1 @
% 1.28/1.48              A @ 
% 1.28/1.48              ( k1_zfmisc_1 @
% 1.28/1.48                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 1.28/1.48    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 1.28/1.48  thf('46', plain,
% 1.28/1.48      ((~ (v1_funct_1 @ sk_A)
% 1.28/1.48        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 1.28/1.48        | ~ (m1_subset_1 @ sk_A @ 
% 1.28/1.48             (k1_zfmisc_1 @ 
% 1.28/1.48              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.28/1.48  thf('47', plain,
% 1.28/1.48      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 1.28/1.48         <= (~
% 1.28/1.48             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 1.28/1.48      inference('split', [status(esa)], ['46'])).
% 1.28/1.48  thf('48', plain,
% 1.28/1.48      (((~ (v1_funct_2 @ sk_A @ k1_xboole_0 @ (k2_relat_1 @ sk_A))
% 1.28/1.48         | ~ (v1_xboole_0 @ sk_A)))
% 1.28/1.48         <= (~
% 1.28/1.48             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 1.28/1.48      inference('sup-', [status(thm)], ['45', '47'])).
% 1.28/1.48  thf('49', plain, ((v1_funct_1 @ sk_A)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.28/1.48  thf('50', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 1.28/1.48      inference('split', [status(esa)], ['46'])).
% 1.28/1.48  thf('51', plain, (((v1_funct_1 @ sk_A))),
% 1.28/1.48      inference('sup-', [status(thm)], ['49', '50'])).
% 1.28/1.48  thf('52', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 1.28/1.48      inference('demod', [status(thm)], ['5', '6'])).
% 1.28/1.48  thf(t3_subset, axiom,
% 1.28/1.48    (![A:$i,B:$i]:
% 1.28/1.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.28/1.48  thf('53', plain,
% 1.28/1.48      (![X9 : $i, X10 : $i]:
% 1.28/1.48         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.28/1.48      inference('cnf', [status(esa)], [t3_subset])).
% 1.28/1.48  thf('54', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.28/1.48      inference('sup-', [status(thm)], ['52', '53'])).
% 1.28/1.48  thf('55', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.28/1.48      inference('sup-', [status(thm)], ['52', '53'])).
% 1.28/1.48  thf(t11_relset_1, axiom,
% 1.28/1.48    (![A:$i,B:$i,C:$i]:
% 1.28/1.48     ( ( v1_relat_1 @ C ) =>
% 1.28/1.48       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.28/1.48           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.28/1.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.28/1.48  thf('56', plain,
% 1.28/1.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.28/1.48         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 1.28/1.48          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ X21)
% 1.28/1.48          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.28/1.48          | ~ (v1_relat_1 @ X19))),
% 1.28/1.48      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.28/1.48  thf('57', plain,
% 1.28/1.48      (![X0 : $i, X1 : $i]:
% 1.28/1.48         (~ (v1_relat_1 @ X0)
% 1.28/1.48          | (m1_subset_1 @ X0 @ 
% 1.28/1.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.28/1.48          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.28/1.48      inference('sup-', [status(thm)], ['55', '56'])).
% 1.28/1.48  thf('58', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((m1_subset_1 @ X0 @ 
% 1.28/1.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.28/1.48          | ~ (v1_relat_1 @ X0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['54', '57'])).
% 1.28/1.48  thf('59', plain,
% 1.28/1.48      ((~ (m1_subset_1 @ sk_A @ 
% 1.28/1.48           (k1_zfmisc_1 @ 
% 1.28/1.48            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 1.28/1.48         <= (~
% 1.28/1.48             ((m1_subset_1 @ sk_A @ 
% 1.28/1.48               (k1_zfmisc_1 @ 
% 1.28/1.48                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 1.28/1.48      inference('split', [status(esa)], ['46'])).
% 1.28/1.48  thf('60', plain,
% 1.28/1.48      ((~ (v1_relat_1 @ sk_A))
% 1.28/1.48         <= (~
% 1.28/1.48             ((m1_subset_1 @ sk_A @ 
% 1.28/1.48               (k1_zfmisc_1 @ 
% 1.28/1.48                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 1.28/1.48      inference('sup-', [status(thm)], ['58', '59'])).
% 1.28/1.48  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.28/1.48  thf('62', plain,
% 1.28/1.48      (((m1_subset_1 @ sk_A @ 
% 1.28/1.48         (k1_zfmisc_1 @ 
% 1.28/1.48          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 1.28/1.48      inference('demod', [status(thm)], ['60', '61'])).
% 1.28/1.48  thf('63', plain,
% 1.28/1.48      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 1.28/1.48       ~
% 1.28/1.48       ((m1_subset_1 @ sk_A @ 
% 1.28/1.48         (k1_zfmisc_1 @ 
% 1.28/1.48          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 1.28/1.48       ~ ((v1_funct_1 @ sk_A))),
% 1.28/1.48      inference('split', [status(esa)], ['46'])).
% 1.28/1.48  thf('64', plain,
% 1.28/1.48      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 1.28/1.48      inference('sat_resolution*', [status(thm)], ['51', '62', '63'])).
% 1.28/1.48  thf('65', plain,
% 1.28/1.48      ((~ (v1_funct_2 @ sk_A @ k1_xboole_0 @ (k2_relat_1 @ sk_A))
% 1.28/1.48        | ~ (v1_xboole_0 @ sk_A))),
% 1.28/1.48      inference('simpl_trail', [status(thm)], ['48', '64'])).
% 1.28/1.48  thf('66', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_A))),
% 1.28/1.48      inference('sup-', [status(thm)], ['44', '65'])).
% 1.28/1.48  thf('67', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.28/1.48      inference('simplify', [status(thm)], ['66'])).
% 1.28/1.48  thf('68', plain,
% 1.28/1.48      (![X22 : $i, X23 : $i]:
% 1.28/1.48         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.28/1.48  thf('69', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((m1_subset_1 @ X0 @ 
% 1.28/1.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.28/1.48          | ~ (v1_relat_1 @ X0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['54', '57'])).
% 1.28/1.48  thf('70', plain,
% 1.28/1.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.28/1.48         (~ (zip_tseitin_0 @ X27 @ X28)
% 1.28/1.48          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 1.28/1.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.28/1.48  thf('71', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         (~ (v1_relat_1 @ X0)
% 1.28/1.48          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.28/1.48          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.28/1.48      inference('sup-', [status(thm)], ['69', '70'])).
% 1.28/1.48  thf('72', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.28/1.48          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.28/1.48          | ~ (v1_relat_1 @ X0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['68', '71'])).
% 1.28/1.48  thf('73', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((m1_subset_1 @ X0 @ 
% 1.28/1.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.28/1.48          | ~ (v1_relat_1 @ X0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['54', '57'])).
% 1.28/1.48  thf('74', plain,
% 1.28/1.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.28/1.48         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.28/1.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.28/1.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.28/1.48  thf('75', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         (~ (v1_relat_1 @ X0)
% 1.28/1.48          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.28/1.48              = (k1_relat_1 @ X0)))),
% 1.28/1.48      inference('sup-', [status(thm)], ['73', '74'])).
% 1.28/1.48  thf('76', plain,
% 1.28/1.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.28/1.48         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 1.28/1.48          | (v1_funct_2 @ X26 @ X24 @ X25)
% 1.28/1.48          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.48  thf('77', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 1.28/1.48          | ~ (v1_relat_1 @ X0)
% 1.28/1.48          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.28/1.48          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.28/1.48      inference('sup-', [status(thm)], ['75', '76'])).
% 1.28/1.48  thf('78', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.28/1.48          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.28/1.48          | ~ (v1_relat_1 @ X0))),
% 1.28/1.48      inference('simplify', [status(thm)], ['77'])).
% 1.28/1.48  thf('79', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         (~ (v1_relat_1 @ X0)
% 1.28/1.48          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.28/1.48          | ~ (v1_relat_1 @ X0)
% 1.28/1.48          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.28/1.48      inference('sup-', [status(thm)], ['72', '78'])).
% 1.28/1.48  thf('80', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.28/1.48          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.28/1.48          | ~ (v1_relat_1 @ X0))),
% 1.28/1.48      inference('simplify', [status(thm)], ['79'])).
% 1.28/1.48  thf('81', plain,
% 1.28/1.48      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 1.28/1.48         <= (~
% 1.28/1.48             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 1.28/1.48      inference('split', [status(esa)], ['46'])).
% 1.28/1.48  thf('82', plain,
% 1.28/1.48      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 1.28/1.48      inference('sat_resolution*', [status(thm)], ['51', '62', '63'])).
% 1.28/1.48  thf('83', plain,
% 1.28/1.48      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 1.28/1.48      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 1.28/1.48  thf('84', plain,
% 1.28/1.48      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 1.28/1.48      inference('sup-', [status(thm)], ['80', '83'])).
% 1.28/1.48  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.28/1.48  thf('86', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 1.28/1.48      inference('demod', [status(thm)], ['84', '85'])).
% 1.28/1.48  thf('87', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         ((m1_subset_1 @ X0 @ 
% 1.28/1.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.28/1.48          | ~ (v1_relat_1 @ X0))),
% 1.28/1.48      inference('sup-', [status(thm)], ['54', '57'])).
% 1.28/1.48  thf(cc4_relset_1, axiom,
% 1.28/1.48    (![A:$i,B:$i]:
% 1.28/1.48     ( ( v1_xboole_0 @ A ) =>
% 1.28/1.48       ( ![C:$i]:
% 1.28/1.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.28/1.48           ( v1_xboole_0 @ C ) ) ) ))).
% 1.28/1.48  thf('88', plain,
% 1.28/1.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.28/1.48         (~ (v1_xboole_0 @ X13)
% 1.28/1.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 1.28/1.48          | (v1_xboole_0 @ X14))),
% 1.28/1.48      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.28/1.48  thf('89', plain,
% 1.28/1.48      (![X0 : $i]:
% 1.28/1.48         (~ (v1_relat_1 @ X0)
% 1.28/1.48          | (v1_xboole_0 @ X0)
% 1.28/1.48          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 1.28/1.48      inference('sup-', [status(thm)], ['87', '88'])).
% 1.28/1.48  thf('90', plain,
% 1.28/1.48      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.28/1.48        | (v1_xboole_0 @ sk_A)
% 1.28/1.48        | ~ (v1_relat_1 @ sk_A))),
% 1.28/1.48      inference('sup-', [status(thm)], ['86', '89'])).
% 1.28/1.48  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.28/1.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.28/1.48  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 1.28/1.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.28/1.48  thf('93', plain, ((v1_xboole_0 @ sk_A)),
% 1.28/1.48      inference('demod', [status(thm)], ['90', '91', '92'])).
% 1.28/1.48  thf('94', plain, ($false), inference('demod', [status(thm)], ['67', '93'])).
% 1.28/1.48  
% 1.28/1.48  % SZS output end Refutation
% 1.28/1.48  
% 1.28/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
