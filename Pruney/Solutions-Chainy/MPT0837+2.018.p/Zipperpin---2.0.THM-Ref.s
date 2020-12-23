%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pu7bVDvvV2

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 155 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  819 (1825 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,(
    ! [X39: $i] :
      ( ~ ( m1_subset_1 @ X39 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X39 @ sk_D_4 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X39: $i] :
        ( ~ ( m1_subset_1 @ X39 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X39 @ sk_D_4 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X29: $i] :
      ( ( ( k9_relat_1 @ X29 @ ( k1_relat_1 @ X29 ) )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k9_relat_1 @ X28 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X28 @ X26 @ X27 ) @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_D_4 ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_D_4 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ! [X39: $i] :
        ( ~ ( m1_subset_1 @ X39 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X39 @ sk_D_4 ) @ sk_C_1 ) )
   <= ! [X39: $i] :
        ( ~ ( m1_subset_1 @ X39 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X39 @ sk_D_4 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_3 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( ! [X39: $i] :
          ( ~ ( m1_subset_1 @ X39 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X39 @ sk_D_4 ) @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('22',plain,(
    ! [X29: $i] :
      ( ( ( k9_relat_1 @ X29 @ ( k1_relat_1 @ X29 ) )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k9_relat_1 @ X28 @ X26 ) )
      | ( r2_hidden @ ( sk_D_3 @ X28 @ X26 @ X27 ) @ X26 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_3 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X30 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('49',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_4 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ! [X39: $i] :
          ( ~ ( m1_subset_1 @ X39 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X39 @ sk_D_4 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['20','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('52',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k2_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k2_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','50','51','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pu7bVDvvV2
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:59:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.34  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 192 iterations in 0.089s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.53  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.19/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.53  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.19/0.53  thf(t48_relset_1, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.53               ( ![D:$i]:
% 0.19/0.53                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.19/0.53                   ( ?[E:$i]:
% 0.19/0.53                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.19/0.53                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.53              ( ![C:$i]:
% 0.19/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.53                  ( ![D:$i]:
% 0.19/0.53                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.19/0.53                      ( ?[E:$i]:
% 0.19/0.53                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.19/0.53                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      (![X39 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X39 @ sk_B)
% 0.19/0.53          | ~ (r2_hidden @ (k4_tarski @ X39 @ sk_D_4) @ sk_C_1)
% 0.19/0.53          | ~ (r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      ((![X39 : $i]:
% 0.19/0.53          (~ (m1_subset_1 @ X39 @ sk_B)
% 0.19/0.53           | ~ (r2_hidden @ (k4_tarski @ X39 @ sk_D_4) @ sk_C_1))) | 
% 0.19/0.53       ~ ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.19/0.53         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.19/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_1)
% 0.19/0.53        | (r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('split', [status(esa)], ['5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (((r2_hidden @ sk_D_4 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('sup+', [status(thm)], ['4', '6'])).
% 0.19/0.53  thf(t146_relat_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ A ) =>
% 0.19/0.53       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X29 : $i]:
% 0.19/0.53         (((k9_relat_1 @ X29 @ (k1_relat_1 @ X29)) = (k2_relat_1 @ X29))
% 0.19/0.53          | ~ (v1_relat_1 @ X29))),
% 0.19/0.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.19/0.53  thf(t143_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ C ) =>
% 0.19/0.53       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.19/0.53         ( ?[D:$i]:
% 0.19/0.53           ( ( r2_hidden @ D @ B ) & 
% 0.19/0.53             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.19/0.53             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X27 @ (k9_relat_1 @ X28 @ X26))
% 0.19/0.53          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X28 @ X26 @ X27) @ X27) @ X28)
% 0.19/0.53          | ~ (v1_relat_1 @ X28))),
% 0.19/0.53      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | (r2_hidden @ 
% 0.19/0.53             (k4_tarski @ (sk_D_3 @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r2_hidden @ 
% 0.19/0.53           (k4_tarski @ (sk_D_3 @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (((~ (v1_relat_1 @ sk_C_1)
% 0.19/0.53         | (r2_hidden @ 
% 0.19/0.53            (k4_tarski @ (sk_D_3 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.19/0.53             sk_D_4) @ 
% 0.19/0.53            sk_C_1)))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['7', '11'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(cc2_relat_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.19/0.53          | (v1_relat_1 @ X14)
% 0.19/0.53          | ~ (v1_relat_1 @ X15))),
% 0.19/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf(fc6_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.19/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.53  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (((r2_hidden @ 
% 0.19/0.53         (k4_tarski @ (sk_D_3 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.19/0.53          sk_D_4) @ 
% 0.19/0.53         sk_C_1))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('demod', [status(thm)], ['12', '17'])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      ((![X39 : $i]:
% 0.19/0.53          (~ (m1_subset_1 @ X39 @ sk_B)
% 0.19/0.53           | ~ (r2_hidden @ (k4_tarski @ X39 @ sk_D_4) @ sk_C_1)))
% 0.19/0.53         <= ((![X39 : $i]:
% 0.19/0.53                (~ (m1_subset_1 @ X39 @ sk_B)
% 0.19/0.53                 | ~ (r2_hidden @ (k4_tarski @ X39 @ sk_D_4) @ sk_C_1))))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      ((~ (m1_subset_1 @ (sk_D_3 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.19/0.53           sk_B))
% 0.19/0.53         <= ((![X39 : $i]:
% 0.19/0.53                (~ (m1_subset_1 @ X39 @ sk_B)
% 0.19/0.53                 | ~ (r2_hidden @ (k4_tarski @ X39 @ sk_D_4) @ sk_C_1))) & 
% 0.19/0.53             ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (((r2_hidden @ sk_D_4 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('sup+', [status(thm)], ['4', '6'])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X29 : $i]:
% 0.19/0.53         (((k9_relat_1 @ X29 @ (k1_relat_1 @ X29)) = (k2_relat_1 @ X29))
% 0.19/0.53          | ~ (v1_relat_1 @ X29))),
% 0.19/0.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X27 @ (k9_relat_1 @ X28 @ X26))
% 0.19/0.53          | (r2_hidden @ (sk_D_3 @ X28 @ X26 @ X27) @ X26)
% 0.19/0.53          | ~ (v1_relat_1 @ X28))),
% 0.19/0.53      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | (r2_hidden @ (sk_D_3 @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.19/0.53             (k1_relat_1 @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r2_hidden @ (sk_D_3 @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.19/0.53           (k1_relat_1 @ X0))
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (((~ (v1_relat_1 @ sk_C_1)
% 0.19/0.53         | (r2_hidden @ (sk_D_3 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.19/0.53            (k1_relat_1 @ sk_C_1))))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['21', '25'])).
% 0.19/0.53  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (((r2_hidden @ (sk_D_3 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.19/0.53         (k1_relat_1 @ sk_C_1)))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(dt_k1_relset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.53       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.53         ((m1_subset_1 @ (k1_relset_1 @ X30 @ X31 @ X32) @ (k1_zfmisc_1 @ X30))
% 0.19/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ 
% 0.19/0.53        (k1_zfmisc_1 @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.53         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.19/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['31', '34'])).
% 0.19/0.53  thf(dt_k3_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      (![X8 : $i, X9 : $i]:
% 0.19/0.53         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.19/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k1_relat_1 @ sk_C_1)) @ 
% 0.19/0.53        (k1_zfmisc_1 @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.53  thf(d5_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.19/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.53  thf('39', plain,
% 0.19/0.53      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_relat_1 @ sk_C_1)))
% 0.19/0.53         = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.53  thf('40', plain,
% 0.19/0.53      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.53      inference('demod', [status(thm)], ['31', '34'])).
% 0.19/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      (![X10 : $i, X11 : $i]:
% 0.19/0.53         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.19/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.19/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_relat_1 @ sk_C_1)))
% 0.19/0.53         = (k1_relat_1 @ sk_C_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.53  thf('43', plain,
% 0.19/0.53      (((k1_relat_1 @ sk_C_1)
% 0.19/0.53         = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.19/0.53      inference('demod', [status(thm)], ['39', '42'])).
% 0.19/0.53  thf(d5_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.53       ( ![D:$i]:
% 0.19/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.53          | (r2_hidden @ X4 @ X1)
% 0.19/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.53         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)) | (r2_hidden @ X0 @ sk_B))),
% 0.19/0.53      inference('sup-', [status(thm)], ['43', '45'])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      (((r2_hidden @ (sk_D_3 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_4) @ sk_B))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['28', '46'])).
% 0.19/0.53  thf(t1_subset, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.53  thf('48', plain,
% 0.19/0.53      (![X12 : $i, X13 : $i]:
% 0.19/0.53         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.53  thf('49', plain,
% 0.19/0.53      (((m1_subset_1 @ (sk_D_3 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_4) @ 
% 0.19/0.53         sk_B))
% 0.19/0.53         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.53  thf('50', plain,
% 0.19/0.53      (~
% 0.19/0.53       (![X39 : $i]:
% 0.19/0.53          (~ (m1_subset_1 @ X39 @ sk_B)
% 0.19/0.53           | ~ (r2_hidden @ (k4_tarski @ X39 @ sk_D_4) @ sk_C_1))) | 
% 0.19/0.53       ~ ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('demod', [status(thm)], ['20', '49'])).
% 0.19/0.53  thf('51', plain,
% 0.19/0.53      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_1)) | 
% 0.19/0.53       ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('split', [status(esa)], ['5'])).
% 0.19/0.53  thf('52', plain,
% 0.19/0.53      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_1))
% 0.19/0.53         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_1)))),
% 0.19/0.53      inference('split', [status(esa)], ['5'])).
% 0.19/0.53  thf(d5_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.19/0.53       ( ![C:$i]:
% 0.19/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.19/0.53  thf('53', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.53         (~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18)
% 0.19/0.53          | (r2_hidden @ X17 @ X19)
% 0.19/0.53          | ((X19) != (k2_relat_1 @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.19/0.53  thf('54', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.53         ((r2_hidden @ X17 @ (k2_relat_1 @ X18))
% 0.19/0.53          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18))),
% 0.19/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.19/0.53  thf('55', plain,
% 0.19/0.53      (((r2_hidden @ sk_D_4 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.53         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['52', '54'])).
% 0.19/0.53  thf('56', plain,
% 0.19/0.53      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.53  thf('57', plain,
% 0.19/0.53      ((~ (r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('58', plain,
% 0.19/0.53      ((~ (r2_hidden @ sk_D_4 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.19/0.53  thf('59', plain,
% 0.19/0.53      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_1)) | 
% 0.19/0.53       ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['55', '58'])).
% 0.19/0.53  thf('60', plain, ($false),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['1', '50', '51', '59'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
