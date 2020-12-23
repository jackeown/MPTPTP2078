%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ihHk0TNSMn

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:05 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 212 expanded)
%              Number of leaves         :   42 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  916 (2349 expanded)
%              Number of equality atoms :   44 ( 106 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_relset_1 @ X45 @ X44 @ ( k3_relset_1 @ X44 @ X45 @ X46 ) )
        = ( k1_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k3_relset_1 @ X42 @ X43 @ X41 )
        = ( k4_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('5',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X32 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('12',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X25 ) )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('22',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['20','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X44 @ ( k3_relset_1 @ X44 @ X45 @ X46 ) )
        = ( k2_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    = ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('42',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('53',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['55','56'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v5_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['59','64'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('70',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('71',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('72',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('73',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('77',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('78',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('82',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ X47 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X47 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('85',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['80','86'])).

thf('88',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['29','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ihHk0TNSMn
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:05:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.83/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.05  % Solved by: fo/fo7.sh
% 0.83/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.05  % done 551 iterations in 0.598s
% 0.83/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.05  % SZS output start Refutation
% 0.83/1.05  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.83/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.05  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.83/1.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.05  thf(sk_B_type, type, sk_B: $i > $i).
% 0.83/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.05  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.83/1.05  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.83/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.05  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.83/1.05  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.83/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.05  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.83/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.83/1.05  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.83/1.05  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.83/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.05  thf(t49_relset_1, conjecture,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.83/1.05           ( ![C:$i]:
% 0.83/1.05             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.05               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.83/1.05                    ( ![D:$i]:
% 0.83/1.05                      ( ( m1_subset_1 @ D @ B ) =>
% 0.83/1.05                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.05    (~( ![A:$i]:
% 0.83/1.05        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.83/1.05          ( ![B:$i]:
% 0.83/1.05            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.83/1.05              ( ![C:$i]:
% 0.83/1.05                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.05                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.83/1.05                       ( ![D:$i]:
% 0.83/1.05                         ( ( m1_subset_1 @ D @ B ) =>
% 0.83/1.05                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.83/1.05    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.83/1.05  thf('0', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(t24_relset_1, axiom,
% 0.83/1.05    (![A:$i,B:$i,C:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.05       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.83/1.05           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.83/1.05         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.83/1.05           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.83/1.05  thf('1', plain,
% 0.83/1.05      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.83/1.05         (((k2_relset_1 @ X45 @ X44 @ (k3_relset_1 @ X44 @ X45 @ X46))
% 0.83/1.05            = (k1_relset_1 @ X44 @ X45 @ X46))
% 0.83/1.05          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.83/1.05      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.83/1.05  thf('2', plain,
% 0.83/1.05      (((k2_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.83/1.05         = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['0', '1'])).
% 0.83/1.05  thf('3', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(redefinition_k3_relset_1, axiom,
% 0.83/1.05    (![A:$i,B:$i,C:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.05       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.83/1.05  thf('4', plain,
% 0.83/1.05      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.83/1.05         (((k3_relset_1 @ X42 @ X43 @ X41) = (k4_relat_1 @ X41))
% 0.83/1.05          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.83/1.05      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.83/1.05  thf('5', plain,
% 0.83/1.05      (((k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['3', '4'])).
% 0.83/1.05  thf('6', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(redefinition_k1_relset_1, axiom,
% 0.83/1.05    (![A:$i,B:$i,C:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.05       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.83/1.05  thf('7', plain,
% 0.83/1.05      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.83/1.05         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.83/1.05          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.83/1.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.83/1.05  thf('8', plain,
% 0.83/1.05      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.05  thf('9', plain,
% 0.83/1.05      (((k2_relset_1 @ sk_B_1 @ sk_A @ (k4_relat_1 @ sk_C_1))
% 0.83/1.05         = (k1_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('demod', [status(thm)], ['2', '5', '8'])).
% 0.83/1.05  thf('10', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(dt_k3_relset_1, axiom,
% 0.83/1.05    (![A:$i,B:$i,C:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.05       ( m1_subset_1 @
% 0.83/1.05         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.83/1.05         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.83/1.05  thf('11', plain,
% 0.83/1.05      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.83/1.05         ((m1_subset_1 @ (k3_relset_1 @ X32 @ X33 @ X34) @ 
% 0.83/1.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.83/1.05          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.83/1.05      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.83/1.05  thf('12', plain,
% 0.83/1.05      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 0.83/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['10', '11'])).
% 0.83/1.05  thf(redefinition_k2_relset_1, axiom,
% 0.83/1.05    (![A:$i,B:$i,C:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.05       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.83/1.05  thf('13', plain,
% 0.83/1.05      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.83/1.05         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.83/1.05          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.83/1.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.05  thf('14', plain,
% 0.83/1.05      (((k2_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.83/1.05         = (k2_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['12', '13'])).
% 0.83/1.05  thf('15', plain,
% 0.83/1.05      (((k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['3', '4'])).
% 0.83/1.05  thf('16', plain,
% 0.83/1.05      (((k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['3', '4'])).
% 0.83/1.05  thf('17', plain,
% 0.83/1.05      (((k2_relset_1 @ sk_B_1 @ sk_A @ (k4_relat_1 @ sk_C_1))
% 0.83/1.05         = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.83/1.05  thf('18', plain,
% 0.83/1.05      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['9', '17'])).
% 0.83/1.05  thf(fc11_relat_1, axiom,
% 0.83/1.05    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.83/1.05  thf('19', plain,
% 0.83/1.05      (![X25 : $i]:
% 0.83/1.05         ((v1_xboole_0 @ (k2_relat_1 @ X25)) | ~ (v1_xboole_0 @ X25))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.83/1.05  thf('20', plain,
% 0.83/1.05      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 0.83/1.05        | ~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['18', '19'])).
% 0.83/1.05  thf(t8_boole, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.83/1.05  thf('21', plain,
% 0.83/1.05      (![X3 : $i, X4 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t8_boole])).
% 0.83/1.05  thf('22', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (k1_xboole_0))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('23', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((X0) != (k1_xboole_0))
% 0.83/1.05          | ~ (v1_xboole_0 @ (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.83/1.05          | ~ (v1_xboole_0 @ X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['21', '22'])).
% 0.83/1.05  thf('24', plain,
% 0.83/1.05      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.05        | ~ (v1_xboole_0 @ (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.83/1.05      inference('simplify', [status(thm)], ['23'])).
% 0.83/1.05  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.05  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.05  thf('26', plain, (~ (v1_xboole_0 @ (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.83/1.05      inference('simplify_reflect+', [status(thm)], ['24', '25'])).
% 0.83/1.05  thf('27', plain,
% 0.83/1.05      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.05  thf('28', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.83/1.05  thf('29', plain, (~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('clc', [status(thm)], ['20', '28'])).
% 0.83/1.05  thf('30', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('31', plain,
% 0.83/1.05      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.83/1.05         (((k1_relset_1 @ X45 @ X44 @ (k3_relset_1 @ X44 @ X45 @ X46))
% 0.83/1.05            = (k2_relset_1 @ X44 @ X45 @ X46))
% 0.83/1.05          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.83/1.05      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.83/1.05  thf('32', plain,
% 0.83/1.05      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.83/1.05         = (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['30', '31'])).
% 0.83/1.05  thf('33', plain,
% 0.83/1.05      (((k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['3', '4'])).
% 0.83/1.05  thf('34', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('35', plain,
% 0.83/1.05      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.83/1.05         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.83/1.05          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.83/1.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.05  thf('36', plain,
% 0.83/1.05      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.05  thf('37', plain,
% 0.83/1.05      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k4_relat_1 @ sk_C_1))
% 0.83/1.05         = (k2_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('demod', [status(thm)], ['32', '33', '36'])).
% 0.83/1.05  thf('38', plain,
% 0.83/1.05      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 0.83/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['10', '11'])).
% 0.83/1.05  thf('39', plain,
% 0.83/1.05      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.83/1.05         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.83/1.05          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.83/1.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.83/1.05  thf('40', plain,
% 0.83/1.05      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.83/1.05         = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['38', '39'])).
% 0.83/1.05  thf('41', plain,
% 0.83/1.05      (((k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['3', '4'])).
% 0.83/1.05  thf('42', plain,
% 0.83/1.05      (((k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['3', '4'])).
% 0.83/1.05  thf('43', plain,
% 0.83/1.05      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k4_relat_1 @ sk_C_1))
% 0.83/1.05         = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.83/1.05  thf('44', plain,
% 0.83/1.05      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['37', '43'])).
% 0.83/1.05  thf(fc8_relat_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.83/1.05       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.83/1.05  thf('45', plain,
% 0.83/1.05      (![X28 : $i]:
% 0.83/1.05         (~ (v1_xboole_0 @ (k1_relat_1 @ X28))
% 0.83/1.05          | ~ (v1_relat_1 @ X28)
% 0.83/1.05          | (v1_xboole_0 @ X28))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.83/1.05  thf('46', plain,
% 0.83/1.05      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.83/1.05        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1))
% 0.83/1.05        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['44', '45'])).
% 0.83/1.05  thf('47', plain,
% 0.83/1.05      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) @ 
% 0.83/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['10', '11'])).
% 0.83/1.05  thf(cc2_relat_1, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( v1_relat_1 @ A ) =>
% 0.83/1.05       ( ![B:$i]:
% 0.83/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.83/1.05  thf('48', plain,
% 0.83/1.05      (![X21 : $i, X22 : $i]:
% 0.83/1.05         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.83/1.05          | (v1_relat_1 @ X21)
% 0.83/1.05          | ~ (v1_relat_1 @ X22))),
% 0.83/1.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.83/1.05  thf('49', plain,
% 0.83/1.05      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))
% 0.83/1.05        | (v1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['47', '48'])).
% 0.83/1.05  thf(fc6_relat_1, axiom,
% 0.83/1.05    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.83/1.05  thf('50', plain,
% 0.83/1.05      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.83/1.05  thf('51', plain, ((v1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.83/1.05      inference('demod', [status(thm)], ['49', '50'])).
% 0.83/1.05  thf('52', plain,
% 0.83/1.05      (((k3_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['3', '4'])).
% 0.83/1.05  thf('53', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('demod', [status(thm)], ['51', '52'])).
% 0.83/1.05  thf('54', plain,
% 0.83/1.05      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.83/1.05        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('demod', [status(thm)], ['46', '53'])).
% 0.83/1.05  thf('55', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf(cc2_relset_1, axiom,
% 0.83/1.05    (![A:$i,B:$i,C:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.83/1.05  thf('56', plain,
% 0.83/1.05      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.83/1.05         ((v5_relat_1 @ X29 @ X31)
% 0.83/1.05          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.83/1.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.83/1.05  thf('57', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.83/1.05      inference('sup-', [status(thm)], ['55', '56'])).
% 0.83/1.05  thf(d19_relat_1, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( v1_relat_1 @ B ) =>
% 0.83/1.05       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.83/1.05  thf('58', plain,
% 0.83/1.05      (![X23 : $i, X24 : $i]:
% 0.83/1.05         (~ (v5_relat_1 @ X23 @ X24)
% 0.83/1.05          | (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.83/1.05          | ~ (v1_relat_1 @ X23))),
% 0.83/1.05      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.83/1.05  thf('59', plain,
% 0.83/1.05      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['57', '58'])).
% 0.83/1.05  thf('60', plain,
% 0.83/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('61', plain,
% 0.83/1.05      (![X21 : $i, X22 : $i]:
% 0.83/1.05         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.83/1.05          | (v1_relat_1 @ X21)
% 0.83/1.05          | ~ (v1_relat_1 @ X22))),
% 0.83/1.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.83/1.05  thf('62', plain,
% 0.83/1.05      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['60', '61'])).
% 0.83/1.05  thf('63', plain,
% 0.83/1.05      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.83/1.05  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 0.83/1.05      inference('demod', [status(thm)], ['62', '63'])).
% 0.83/1.05  thf('65', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.83/1.05      inference('demod', [status(thm)], ['59', '64'])).
% 0.83/1.05  thf(t3_subset, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.05  thf('66', plain,
% 0.83/1.05      (![X18 : $i, X20 : $i]:
% 0.83/1.05         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.83/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.05  thf('67', plain,
% 0.83/1.05      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['65', '66'])).
% 0.83/1.05  thf(t2_subset, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( m1_subset_1 @ A @ B ) =>
% 0.83/1.05       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.83/1.05  thf('68', plain,
% 0.83/1.05      (![X16 : $i, X17 : $i]:
% 0.83/1.05         ((r2_hidden @ X16 @ X17)
% 0.83/1.05          | (v1_xboole_0 @ X17)
% 0.83/1.05          | ~ (m1_subset_1 @ X16 @ X17))),
% 0.83/1.05      inference('cnf', [status(esa)], [t2_subset])).
% 0.83/1.05  thf('69', plain,
% 0.83/1.05      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.83/1.05        | (r2_hidden @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['67', '68'])).
% 0.83/1.05  thf(fc1_subset_1, axiom,
% 0.83/1.05    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.83/1.05  thf('70', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.83/1.05      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.83/1.05  thf('71', plain,
% 0.83/1.05      ((r2_hidden @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.83/1.05      inference('clc', [status(thm)], ['69', '70'])).
% 0.83/1.05  thf(d1_xboole_0, axiom,
% 0.83/1.05    (![A:$i]:
% 0.83/1.05     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.83/1.05  thf('72', plain,
% 0.83/1.05      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.83/1.05      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.83/1.05  thf(d4_tarski, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.83/1.05       ( ![C:$i]:
% 0.83/1.05         ( ( r2_hidden @ C @ B ) <=>
% 0.83/1.05           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.83/1.05  thf('73', plain,
% 0.83/1.05      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.05         (~ (r2_hidden @ X5 @ X6)
% 0.83/1.05          | ~ (r2_hidden @ X7 @ X5)
% 0.83/1.05          | (r2_hidden @ X7 @ X8)
% 0.83/1.05          | ((X8) != (k3_tarski @ X6)))),
% 0.83/1.05      inference('cnf', [status(esa)], [d4_tarski])).
% 0.83/1.05  thf('74', plain,
% 0.83/1.05      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.05         ((r2_hidden @ X7 @ (k3_tarski @ X6))
% 0.83/1.05          | ~ (r2_hidden @ X7 @ X5)
% 0.83/1.05          | ~ (r2_hidden @ X5 @ X6))),
% 0.83/1.05      inference('simplify', [status(thm)], ['73'])).
% 0.83/1.05  thf('75', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((v1_xboole_0 @ X0)
% 0.83/1.05          | ~ (r2_hidden @ X0 @ X1)
% 0.83/1.05          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['72', '74'])).
% 0.83/1.05  thf('76', plain,
% 0.83/1.05      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 0.83/1.05         (k3_tarski @ (k1_zfmisc_1 @ sk_B_1)))
% 0.83/1.05        | (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['71', '75'])).
% 0.83/1.05  thf(t99_zfmisc_1, axiom,
% 0.83/1.05    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.83/1.05  thf('77', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 0.83/1.05      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.83/1.05  thf('78', plain,
% 0.83/1.05      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1)
% 0.83/1.05        | (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.83/1.05      inference('demod', [status(thm)], ['76', '77'])).
% 0.83/1.05  thf(t1_subset, axiom,
% 0.83/1.05    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.83/1.05  thf('79', plain,
% 0.83/1.05      (![X14 : $i, X15 : $i]:
% 0.83/1.05         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.83/1.05      inference('cnf', [status(esa)], [t1_subset])).
% 0.83/1.05  thf('80', plain,
% 0.83/1.05      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.83/1.05        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.05  thf('81', plain,
% 0.83/1.05      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.83/1.05      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.83/1.05  thf('82', plain,
% 0.83/1.05      (![X47 : $i]:
% 0.83/1.05         (~ (r2_hidden @ X47 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.83/1.05          | ~ (m1_subset_1 @ X47 @ sk_B_1))),
% 0.83/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.05  thf('83', plain,
% 0.83/1.05      (((v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.83/1.05        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.83/1.05             sk_B_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['81', '82'])).
% 0.83/1.05  thf('84', plain,
% 0.83/1.05      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.05  thf('85', plain,
% 0.83/1.05      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.05  thf('86', plain,
% 0.83/1.05      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.83/1.05        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.83/1.05      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.83/1.05  thf('87', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('clc', [status(thm)], ['80', '86'])).
% 0.83/1.05  thf('88', plain, ((v1_xboole_0 @ (k4_relat_1 @ sk_C_1))),
% 0.83/1.05      inference('demod', [status(thm)], ['54', '87'])).
% 0.83/1.05  thf('89', plain, ($false), inference('demod', [status(thm)], ['29', '88'])).
% 0.83/1.05  
% 0.83/1.05  % SZS output end Refutation
% 0.83/1.05  
% 0.83/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
