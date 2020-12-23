%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0405+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:16 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  45 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > m1_subset_1 > k6_subset_1 > k4_setfam_1 > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k4_setfam_1,type,(
    k4_setfam_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k6_subset_1(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k4_setfam_1(A,A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_setfam_1)).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_13,B_14,D_40] :
      ( r2_hidden('#skF_7'(A_13,B_14,k4_setfam_1(A_13,B_14),D_40),A_13)
      | ~ r2_hidden(D_40,k4_setfam_1(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_89,B_90,D_91] :
      ( k6_subset_1('#skF_7'(A_89,B_90,k4_setfam_1(A_89,B_90),D_91),'#skF_8'(A_89,B_90,k4_setfam_1(A_89,B_90),D_91)) = D_91
      | ~ r2_hidden(D_91,k4_setfam_1(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_47,B_48] : m1_subset_1(k6_subset_1(A_47,B_48),k1_zfmisc_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_43,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_51,plain,(
    ! [A_47,B_48] : r1_tarski(k6_subset_1(A_47,B_48),A_47) ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_86,plain,(
    ! [D_92,A_93,B_94] :
      ( r1_tarski(D_92,'#skF_7'(A_93,B_94,k4_setfam_1(A_93,B_94),D_92))
      | ~ r2_hidden(D_92,k4_setfam_1(A_93,B_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_51])).

tff(c_6,plain,(
    ! [A_1,B_2,D_10] :
      ( ~ r1_tarski('#skF_1'(A_1,B_2),D_10)
      | ~ r2_hidden(D_10,B_2)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_111,plain,(
    ! [A_110,B_111,A_112,B_113] :
      ( ~ r2_hidden('#skF_7'(A_110,B_111,k4_setfam_1(A_110,B_111),'#skF_1'(A_112,B_113)),B_113)
      | r1_setfam_1(A_112,B_113)
      | ~ r2_hidden('#skF_1'(A_112,B_113),k4_setfam_1(A_110,B_111)) ) ),
    inference(resolution,[status(thm)],[c_86,c_6])).

tff(c_117,plain,(
    ! [A_114,A_115,B_116] :
      ( r1_setfam_1(A_114,A_115)
      | ~ r2_hidden('#skF_1'(A_114,A_115),k4_setfam_1(A_115,B_116)) ) ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_122,plain,(
    ! [B_2,B_116] : r1_setfam_1(k4_setfam_1(B_2,B_116),B_2) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_40,plain,(
    ~ r1_setfam_1(k4_setfam_1('#skF_9','#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_40])).

%------------------------------------------------------------------------------
