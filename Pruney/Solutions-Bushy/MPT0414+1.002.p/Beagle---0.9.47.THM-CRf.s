%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0414+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:16 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   35 (  66 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 150 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    ! [A_26,C_27,B_28] :
      ( m1_subset_1(A_26,C_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [A_30] :
      ( m1_subset_1(A_30,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_30,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_22,plain,(
    ! [D_15] :
      ( r2_hidden(D_15,'#skF_3')
      | ~ r2_hidden(D_15,'#skF_4')
      | ~ m1_subset_1(D_15,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    ! [A_31] :
      ( r2_hidden(A_31,'#skF_3')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_22])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [A_33] :
      ( r1_tarski(A_33,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_33,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_10])).

tff(c_80,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_82,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_82])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ! [A_26] :
      ( m1_subset_1(A_26,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_26,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_86,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,'#skF_4')
      | ~ r2_hidden(D_34,'#skF_3')
      | ~ m1_subset_1(D_34,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_95,plain,(
    ! [A_35] :
      ( r2_hidden(A_35,'#skF_4')
      | ~ r2_hidden(A_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_86])).

tff(c_105,plain,(
    ! [B_36] :
      ( r2_hidden('#skF_1'('#skF_3',B_36),'#skF_4')
      | r1_tarski('#skF_3',B_36) ) ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_115,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_10])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_85,c_115])).

%------------------------------------------------------------------------------
