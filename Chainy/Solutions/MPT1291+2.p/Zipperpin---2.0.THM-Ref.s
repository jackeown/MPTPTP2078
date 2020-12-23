%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1291+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tGyS61Y0ec

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:06 EST 2020

% Result     : Theorem 20.91s
% Output     : Refutation 20.91s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  172 ( 272 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_37_type,type,(
    sk_A_37: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_144_type,type,(
    sk_B_144: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_C_161_type,type,(
    sk_C_161: $i )).

thf(t3_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
         => ! [C: $i] :
              ( ( r1_tarski @ ( C @ B ) )
             => ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
           => ! [C: $i] :
                ( ( r1_tarski @ ( C @ B ) )
               => ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_tops_2])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( sk_C_161 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_37 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('2',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ~ ( m1_subset_1 @ ( sk_C_161 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A_37 ) ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( sk_B_144 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    m1_subset_1 @ ( sk_B_144 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A_37 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('8',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('10',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k9_setfam_1 @ X1965 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( sk_B_144 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A_37 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ ( sk_C_161 @ sk_B_144 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ C ) ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('13',plain,(
    ! [X184: $i,X185: $i,X186: $i] :
      ( ~ ( r1_tarski @ ( X184 @ X185 ) )
      | ~ ( r1_tarski @ ( X185 @ X186 ) )
      | ( r1_tarski @ ( X184 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_C_161 @ X0 ) )
      | ~ ( r1_tarski @ ( sk_B_144 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( sk_C_161 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A_37 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X1964: $i,X1966: $i] :
      ( ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1966 ) ) )
      | ~ ( r1_tarski @ ( X1964 @ X1966 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('18',plain,(
    ! [X1964: $i,X1966: $i] :
      ( ( m1_subset_1 @ ( X1964 @ ( k9_setfam_1 @ X1966 ) ) )
      | ~ ( r1_tarski @ ( X1964 @ X1966 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_C_161 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A_37 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['3','19'])).

%------------------------------------------------------------------------------
