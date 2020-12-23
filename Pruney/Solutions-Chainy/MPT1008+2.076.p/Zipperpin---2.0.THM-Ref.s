%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sZg7N6lfGV

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:42 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 451 expanded)
%              Number of leaves         :   40 ( 156 expanded)
%              Depth                    :   17
%              Number of atoms          : 1099 (5573 expanded)
%              Number of equality atoms :   95 ( 423 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k11_relat_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k11_relat_1 @ X24 @ X23 )
        = ( k1_tarski @ ( k1_funct_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k11_relat_1 @ X12 @ X13 )
        = ( k9_relat_1 @ X12 @ ( k1_tarski @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k7_relset_1 @ X35 @ X36 @ X37 @ X35 )
        = ( k2_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('13',plain,
    ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('18',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('19',plain,
    ( ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('25',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('26',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','23','24','25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k11_relat_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

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

thf('30',plain,(
    ! [X17: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X19
       != ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X17 ) )
      | ( X21
       != ( k1_funct_1 @ X17 @ X22 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('31',plain,(
    ! [X17: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ X22 ) @ ( k2_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k11_relat_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ k1_xboole_0 )
      | ( ( k11_relat_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ( ( k11_relat_1 @ X14 @ X15 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k11_relat_1 @ X12 @ X13 )
        = ( k9_relat_1 @ X12 @ ( k1_tarski @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('46',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('47',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k7_relset_1 @ X35 @ X36 @ X37 @ X35 )
        = ( k2_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1 )
      = ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('53',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','57'])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['37','62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( r2_hidden @ ( sk_D @ X16 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( X16
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X41 @ X38 ) @ ( k2_relset_1 @ X39 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('69',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ ( k1_tarski @ sk_A ) @ X0 ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('83',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('84',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('86',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','87'])).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ( ( k11_relat_1 @ X14 @ X15 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['63','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('94',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['96'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('98',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['83','86'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['99','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sZg7N6lfGV
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:02:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.74/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.98  % Solved by: fo/fo7.sh
% 1.74/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.98  % done 3174 iterations in 1.532s
% 1.74/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.98  % SZS output start Refutation
% 1.74/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.74/1.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.74/1.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.74/1.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.74/1.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.74/1.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.74/1.98  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.74/1.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.74/1.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.74/1.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.74/1.98  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 1.74/1.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.74/1.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.74/1.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.98  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 1.74/1.98  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.74/1.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.74/1.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.74/1.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.74/1.98  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.98  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.74/1.98  thf(t205_relat_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( v1_relat_1 @ B ) =>
% 1.74/1.98       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 1.74/1.98         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 1.74/1.98  thf('0', plain,
% 1.74/1.98      (![X14 : $i, X15 : $i]:
% 1.74/1.98         (((k11_relat_1 @ X14 @ X15) = (k1_xboole_0))
% 1.74/1.98          | (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 1.74/1.98          | ~ (v1_relat_1 @ X14))),
% 1.74/1.98      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.74/1.98  thf(t117_funct_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.74/1.98       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.74/1.98         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.74/1.98  thf('1', plain,
% 1.74/1.98      (![X23 : $i, X24 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 1.74/1.98          | ((k11_relat_1 @ X24 @ X23) = (k1_tarski @ (k1_funct_1 @ X24 @ X23)))
% 1.74/1.98          | ~ (v1_funct_1 @ X24)
% 1.74/1.98          | ~ (v1_relat_1 @ X24))),
% 1.74/1.98      inference('cnf', [status(esa)], [t117_funct_1])).
% 1.74/1.98  thf('2', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (v1_relat_1 @ X0)
% 1.74/1.98          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.74/1.98          | ~ (v1_relat_1 @ X0)
% 1.74/1.98          | ~ (v1_funct_1 @ X0)
% 1.74/1.98          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['0', '1'])).
% 1.74/1.98  thf('3', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1)))
% 1.74/1.98          | ~ (v1_funct_1 @ X0)
% 1.74/1.98          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.74/1.98          | ~ (v1_relat_1 @ X0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['2'])).
% 1.74/1.98  thf(t62_funct_2, conjecture,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.74/1.98         ( m1_subset_1 @
% 1.74/1.98           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.74/1.98       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.74/1.98         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.74/1.98           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.98    (~( ![A:$i,B:$i,C:$i]:
% 1.74/1.98        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.74/1.98            ( m1_subset_1 @
% 1.74/1.98              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.74/1.98          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.74/1.98            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.74/1.98              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 1.74/1.98    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 1.74/1.98  thf('4', plain,
% 1.74/1.98      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 1.74/1.98         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('5', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_C_1 @ 
% 1.74/1.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(redefinition_k2_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.74/1.98  thf('6', plain,
% 1.74/1.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.74/1.98         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 1.74/1.98          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.74/1.98  thf('7', plain,
% 1.74/1.98      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 1.74/1.98         = (k2_relat_1 @ sk_C_1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['5', '6'])).
% 1.74/1.98  thf('8', plain,
% 1.74/1.98      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 1.74/1.98      inference('demod', [status(thm)], ['4', '7'])).
% 1.74/1.98  thf('9', plain,
% 1.74/1.98      ((((k2_relat_1 @ sk_C_1) != (k11_relat_1 @ sk_C_1 @ sk_A))
% 1.74/1.98        | ~ (v1_relat_1 @ sk_C_1)
% 1.74/1.98        | ((k11_relat_1 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 1.74/1.98        | ~ (v1_funct_1 @ sk_C_1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['3', '8'])).
% 1.74/1.98  thf(d16_relat_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( v1_relat_1 @ A ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 1.74/1.98  thf('10', plain,
% 1.74/1.98      (![X12 : $i, X13 : $i]:
% 1.74/1.98         (((k11_relat_1 @ X12 @ X13) = (k9_relat_1 @ X12 @ (k1_tarski @ X13)))
% 1.74/1.98          | ~ (v1_relat_1 @ X12))),
% 1.74/1.98      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.74/1.98  thf('11', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_C_1 @ 
% 1.74/1.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t38_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.74/1.98         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.74/1.98  thf('12', plain,
% 1.74/1.98      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.74/1.98         (((k7_relset_1 @ X35 @ X36 @ X37 @ X35)
% 1.74/1.98            = (k2_relset_1 @ X35 @ X36 @ X37))
% 1.74/1.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.74/1.98      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.74/1.98  thf('13', plain,
% 1.74/1.98      (((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1 @ (k1_tarski @ sk_A))
% 1.74/1.98         = (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['11', '12'])).
% 1.74/1.98  thf('14', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_C_1 @ 
% 1.74/1.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(redefinition_k7_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.74/1.98  thf('15', plain,
% 1.74/1.98      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.74/1.98          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.74/1.98  thf('16', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1 @ X0)
% 1.74/1.98           = (k9_relat_1 @ sk_C_1 @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['14', '15'])).
% 1.74/1.98  thf('17', plain,
% 1.74/1.98      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 1.74/1.98         = (k2_relat_1 @ sk_C_1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['5', '6'])).
% 1.74/1.98  thf('18', plain,
% 1.74/1.98      (((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_C_1))),
% 1.74/1.98      inference('demod', [status(thm)], ['13', '16', '17'])).
% 1.74/1.98  thf('19', plain,
% 1.74/1.98      ((((k11_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 1.74/1.98        | ~ (v1_relat_1 @ sk_C_1))),
% 1.74/1.98      inference('sup+', [status(thm)], ['10', '18'])).
% 1.74/1.98  thf('20', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_C_1 @ 
% 1.74/1.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(cc1_relset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.74/1.98       ( v1_relat_1 @ C ) ))).
% 1.74/1.98  thf('21', plain,
% 1.74/1.98      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.74/1.98         ((v1_relat_1 @ X25)
% 1.74/1.98          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.74/1.98  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 1.74/1.98      inference('sup-', [status(thm)], ['20', '21'])).
% 1.74/1.98  thf('23', plain, (((k11_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))),
% 1.74/1.98      inference('demod', [status(thm)], ['19', '22'])).
% 1.74/1.98  thf('24', plain, ((v1_relat_1 @ sk_C_1)),
% 1.74/1.98      inference('sup-', [status(thm)], ['20', '21'])).
% 1.74/1.98  thf('25', plain, (((k11_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))),
% 1.74/1.98      inference('demod', [status(thm)], ['19', '22'])).
% 1.74/1.98  thf('26', plain, ((v1_funct_1 @ sk_C_1)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('27', plain,
% 1.74/1.98      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 1.74/1.98        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['9', '23', '24', '25', '26'])).
% 1.74/1.98  thf('28', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['27'])).
% 1.74/1.98  thf('29', plain,
% 1.74/1.98      (![X14 : $i, X15 : $i]:
% 1.74/1.98         (((k11_relat_1 @ X14 @ X15) = (k1_xboole_0))
% 1.74/1.98          | (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 1.74/1.98          | ~ (v1_relat_1 @ X14))),
% 1.74/1.98      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.74/1.98  thf(d5_funct_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.74/1.98           ( ![C:$i]:
% 1.74/1.98             ( ( r2_hidden @ C @ B ) <=>
% 1.74/1.98               ( ?[D:$i]:
% 1.74/1.98                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.74/1.98                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.74/1.98  thf('30', plain,
% 1.74/1.98      (![X17 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 1.74/1.98         (((X19) != (k2_relat_1 @ X17))
% 1.74/1.98          | (r2_hidden @ X21 @ X19)
% 1.74/1.98          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X17))
% 1.74/1.98          | ((X21) != (k1_funct_1 @ X17 @ X22))
% 1.74/1.98          | ~ (v1_funct_1 @ X17)
% 1.74/1.98          | ~ (v1_relat_1 @ X17))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.74/1.98  thf('31', plain,
% 1.74/1.98      (![X17 : $i, X22 : $i]:
% 1.74/1.98         (~ (v1_relat_1 @ X17)
% 1.74/1.98          | ~ (v1_funct_1 @ X17)
% 1.74/1.98          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X17))
% 1.74/1.98          | (r2_hidden @ (k1_funct_1 @ X17 @ X22) @ (k2_relat_1 @ X17)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['30'])).
% 1.74/1.98  thf('32', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (v1_relat_1 @ X0)
% 1.74/1.98          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.74/1.98          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 1.74/1.98          | ~ (v1_funct_1 @ X0)
% 1.74/1.98          | ~ (v1_relat_1 @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['29', '31'])).
% 1.74/1.98  thf('33', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (v1_funct_1 @ X0)
% 1.74/1.98          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 1.74/1.98          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.74/1.98          | ~ (v1_relat_1 @ X0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['32'])).
% 1.74/1.98  thf('34', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ k1_xboole_0)
% 1.74/1.98          | ~ (v1_relat_1 @ sk_C_1)
% 1.74/1.98          | ((k11_relat_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 1.74/1.98          | ~ (v1_funct_1 @ sk_C_1))),
% 1.74/1.98      inference('sup+', [status(thm)], ['28', '33'])).
% 1.74/1.98  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 1.74/1.98      inference('sup-', [status(thm)], ['20', '21'])).
% 1.74/1.98  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('37', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ k1_xboole_0)
% 1.74/1.98          | ((k11_relat_1 @ sk_C_1 @ X0) = (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.74/1.98  thf(t60_relat_1, axiom,
% 1.74/1.98    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.74/1.98     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.74/1.98  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.74/1.98  thf('39', plain,
% 1.74/1.98      (![X14 : $i, X15 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 1.74/1.98          | ((k11_relat_1 @ X14 @ X15) != (k1_xboole_0))
% 1.74/1.98          | ~ (v1_relat_1 @ X14))),
% 1.74/1.98      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.74/1.98  thf('40', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.74/1.98          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.74/1.98          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['38', '39'])).
% 1.74/1.98  thf(t4_subset_1, axiom,
% 1.74/1.98    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.74/1.98  thf('41', plain,
% 1.74/1.98      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.74/1.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.74/1.98  thf('42', plain,
% 1.74/1.98      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.74/1.98         ((v1_relat_1 @ X25)
% 1.74/1.98          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.74/1.98  thf('43', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.74/1.98      inference('sup-', [status(thm)], ['41', '42'])).
% 1.74/1.98  thf('44', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.74/1.98          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['40', '43'])).
% 1.74/1.98  thf('45', plain,
% 1.74/1.98      (![X12 : $i, X13 : $i]:
% 1.74/1.98         (((k11_relat_1 @ X12 @ X13) = (k9_relat_1 @ X12 @ (k1_tarski @ X13)))
% 1.74/1.98          | ~ (v1_relat_1 @ X12))),
% 1.74/1.98      inference('cnf', [status(esa)], [d16_relat_1])).
% 1.74/1.98  thf('46', plain,
% 1.74/1.98      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.74/1.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.74/1.98  thf('47', plain,
% 1.74/1.98      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.74/1.98         (((k7_relset_1 @ X35 @ X36 @ X37 @ X35)
% 1.74/1.98            = (k2_relset_1 @ X35 @ X36 @ X37))
% 1.74/1.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.74/1.98      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.74/1.98  thf('48', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1)
% 1.74/1.98           = (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['46', '47'])).
% 1.74/1.98  thf('49', plain,
% 1.74/1.98      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.74/1.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.74/1.98  thf('50', plain,
% 1.74/1.98      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.74/1.98          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.74/1.98  thf('51', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.98         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 1.74/1.98           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 1.74/1.98      inference('sup-', [status(thm)], ['49', '50'])).
% 1.74/1.98  thf('52', plain,
% 1.74/1.98      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.74/1.98      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.74/1.98  thf('53', plain,
% 1.74/1.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.74/1.98         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 1.74/1.98          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.74/1.98  thf('54', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['52', '53'])).
% 1.74/1.98  thf('55', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.74/1.98  thf('56', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['54', '55'])).
% 1.74/1.98  thf('57', plain,
% 1.74/1.98      (![X1 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['48', '51', '56'])).
% 1.74/1.98  thf('58', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 1.74/1.98          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['45', '57'])).
% 1.74/1.98  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.74/1.98      inference('sup-', [status(thm)], ['41', '42'])).
% 1.74/1.98  thf('60', plain,
% 1.74/1.98      (![X0 : $i]: ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['58', '59'])).
% 1.74/1.98  thf('61', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X0 @ k1_xboole_0) | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['44', '60'])).
% 1.74/1.98  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.74/1.98      inference('simplify', [status(thm)], ['61'])).
% 1.74/1.98  thf('63', plain, (![X0 : $i]: ((k11_relat_1 @ sk_C_1 @ X0) = (k1_xboole_0))),
% 1.74/1.98      inference('clc', [status(thm)], ['37', '62'])).
% 1.74/1.98  thf('64', plain,
% 1.74/1.98      (![X16 : $i, X17 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_C @ X16 @ X17) @ X16)
% 1.74/1.98          | (r2_hidden @ (sk_D @ X16 @ X17) @ (k1_relat_1 @ X17))
% 1.74/1.98          | ((X16) = (k2_relat_1 @ X17))
% 1.74/1.98          | ~ (v1_funct_1 @ X17)
% 1.74/1.98          | ~ (v1_relat_1 @ X17))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.74/1.98  thf('65', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_C_1 @ 
% 1.74/1.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t6_funct_2, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.74/1.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.74/1.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.74/1.98       ( ( r2_hidden @ C @ A ) =>
% 1.74/1.98         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.74/1.98           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 1.74/1.98  thf('66', plain,
% 1.74/1.98      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X38 @ X39)
% 1.74/1.98          | ((X40) = (k1_xboole_0))
% 1.74/1.98          | ~ (v1_funct_1 @ X41)
% 1.74/1.98          | ~ (v1_funct_2 @ X41 @ X39 @ X40)
% 1.74/1.98          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.74/1.98          | (r2_hidden @ (k1_funct_1 @ X41 @ X38) @ 
% 1.74/1.98             (k2_relset_1 @ X39 @ X40 @ X41)))),
% 1.74/1.98      inference('cnf', [status(esa)], [t6_funct_2])).
% 1.74/1.98  thf('67', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 1.74/1.98           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))
% 1.74/1.98          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)
% 1.74/1.98          | ~ (v1_funct_1 @ sk_C_1)
% 1.74/1.98          | ((sk_B) = (k1_xboole_0))
% 1.74/1.98          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['65', '66'])).
% 1.74/1.98  thf('68', plain,
% 1.74/1.98      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 1.74/1.98         = (k2_relat_1 @ sk_C_1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['5', '6'])).
% 1.74/1.98  thf('69', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('70', plain, ((v1_funct_1 @ sk_C_1)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('71', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 1.74/1.98          | ((sk_B) = (k1_xboole_0))
% 1.74/1.98          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 1.74/1.98      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 1.74/1.98  thf('72', plain, (((sk_B) != (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('73', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 1.74/1.98          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 1.74/1.98      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 1.74/1.98  thf('74', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (v1_relat_1 @ X0)
% 1.74/1.98          | ~ (v1_funct_1 @ X0)
% 1.74/1.98          | ((k1_tarski @ sk_A) = (k2_relat_1 @ X0))
% 1.74/1.98          | (r2_hidden @ (sk_D @ (k1_tarski @ sk_A) @ X0) @ (k1_relat_1 @ X0))
% 1.74/1.98          | (r2_hidden @ 
% 1.74/1.98             (k1_funct_1 @ sk_C_1 @ (sk_C @ (k1_tarski @ sk_A) @ X0)) @ 
% 1.74/1.98             (k2_relat_1 @ sk_C_1)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['64', '73'])).
% 1.74/1.98  thf(l13_xboole_0, axiom,
% 1.74/1.98    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.74/1.98  thf('75', plain,
% 1.74/1.98      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.74/1.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.74/1.98  thf('76', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 1.74/1.98          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['40', '43'])).
% 1.74/1.98  thf('77', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X1 @ X0)
% 1.74/1.98          | ~ (v1_xboole_0 @ X0)
% 1.74/1.98          | ((k11_relat_1 @ k1_xboole_0 @ X1) != (k1_xboole_0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['75', '76'])).
% 1.74/1.98  thf('78', plain,
% 1.74/1.98      (![X0 : $i]: ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['58', '59'])).
% 1.74/1.98  thf('79', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X1 @ X0)
% 1.74/1.98          | ~ (v1_xboole_0 @ X0)
% 1.74/1.98          | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['77', '78'])).
% 1.74/1.98  thf('80', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['79'])).
% 1.74/1.98  thf('81', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ (k1_tarski @ sk_A) @ X0) @ (k1_relat_1 @ X0))
% 1.74/1.98          | ((k1_tarski @ sk_A) = (k2_relat_1 @ X0))
% 1.74/1.98          | ~ (v1_funct_1 @ X0)
% 1.74/1.98          | ~ (v1_relat_1 @ X0)
% 1.74/1.98          | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['74', '80'])).
% 1.74/1.98  thf('82', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['27'])).
% 1.74/1.98  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 1.74/1.98  thf('83', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 1.74/1.98      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 1.74/1.98  thf('84', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 1.74/1.98      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 1.74/1.98  thf('85', plain,
% 1.74/1.98      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.74/1.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.74/1.98  thf('86', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['84', '85'])).
% 1.74/1.98  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.74/1.98      inference('demod', [status(thm)], ['83', '86'])).
% 1.74/1.98  thf('88', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ (k1_tarski @ sk_A) @ X0) @ (k1_relat_1 @ X0))
% 1.74/1.98          | ((k1_tarski @ sk_A) = (k2_relat_1 @ X0))
% 1.74/1.98          | ~ (v1_funct_1 @ X0)
% 1.74/1.98          | ~ (v1_relat_1 @ X0))),
% 1.74/1.98      inference('demod', [status(thm)], ['81', '82', '87'])).
% 1.74/1.98  thf('89', plain,
% 1.74/1.98      (![X14 : $i, X15 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 1.74/1.98          | ((k11_relat_1 @ X14 @ X15) != (k1_xboole_0))
% 1.74/1.98          | ~ (v1_relat_1 @ X14))),
% 1.74/1.98      inference('cnf', [status(esa)], [t205_relat_1])).
% 1.74/1.98  thf('90', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (v1_relat_1 @ X0)
% 1.74/1.98          | ~ (v1_funct_1 @ X0)
% 1.74/1.98          | ((k1_tarski @ sk_A) = (k2_relat_1 @ X0))
% 1.74/1.98          | ~ (v1_relat_1 @ X0)
% 1.74/1.98          | ((k11_relat_1 @ X0 @ (sk_D @ (k1_tarski @ sk_A) @ X0))
% 1.74/1.98              != (k1_xboole_0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['88', '89'])).
% 1.74/1.98  thf('91', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (((k11_relat_1 @ X0 @ (sk_D @ (k1_tarski @ sk_A) @ X0))
% 1.74/1.98            != (k1_xboole_0))
% 1.74/1.98          | ((k1_tarski @ sk_A) = (k2_relat_1 @ X0))
% 1.74/1.98          | ~ (v1_funct_1 @ X0)
% 1.74/1.98          | ~ (v1_relat_1 @ X0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['90'])).
% 1.74/1.98  thf('92', plain,
% 1.74/1.98      ((((k1_xboole_0) != (k1_xboole_0))
% 1.74/1.98        | ~ (v1_relat_1 @ sk_C_1)
% 1.74/1.98        | ~ (v1_funct_1 @ sk_C_1)
% 1.74/1.98        | ((k1_tarski @ sk_A) = (k2_relat_1 @ sk_C_1)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['63', '91'])).
% 1.74/1.98  thf('93', plain, ((v1_relat_1 @ sk_C_1)),
% 1.74/1.98      inference('sup-', [status(thm)], ['20', '21'])).
% 1.74/1.98  thf('94', plain, ((v1_funct_1 @ sk_C_1)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('95', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['27'])).
% 1.74/1.98  thf('96', plain,
% 1.74/1.98      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 1.74/1.98  thf('97', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['96'])).
% 1.74/1.98  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 1.74/1.98  thf('98', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 1.74/1.98      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 1.74/1.98  thf('99', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 1.74/1.98      inference('sup-', [status(thm)], ['97', '98'])).
% 1.74/1.98  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.74/1.98      inference('demod', [status(thm)], ['83', '86'])).
% 1.74/1.98  thf('101', plain, ($false), inference('demod', [status(thm)], ['99', '100'])).
% 1.74/1.98  
% 1.74/1.98  % SZS output end Refutation
% 1.74/1.98  
% 1.82/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
