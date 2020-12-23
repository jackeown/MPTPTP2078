%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0404+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:16 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  40 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k3_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k3_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k3_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k3_setfam_1(A,A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_setfam_1)).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_13,B_14,D_40] :
      ( r2_hidden('#skF_7'(A_13,B_14,k3_setfam_1(A_13,B_14),D_40),A_13)
      | ~ r2_hidden(D_40,k3_setfam_1(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,(
    ! [A_88,B_89,D_90] :
      ( k3_xboole_0('#skF_7'(A_88,B_89,k3_setfam_1(A_88,B_89),D_90),'#skF_8'(A_88,B_89,k3_setfam_1(A_88,B_89),D_90)) = D_90
      | ~ r2_hidden(D_90,k3_setfam_1(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_47,B_48] : r1_tarski(k3_xboole_0(A_47,B_48),A_47) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [D_96,A_97,B_98] :
      ( r1_tarski(D_96,'#skF_7'(A_97,B_98,k3_setfam_1(A_97,B_98),D_96))
      | ~ r2_hidden(D_96,k3_setfam_1(A_97,B_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_34])).

tff(c_6,plain,(
    ! [A_1,B_2,D_10] :
      ( ~ r1_tarski('#skF_1'(A_1,B_2),D_10)
      | ~ r2_hidden(D_10,B_2)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_86,plain,(
    ! [A_99,B_100,A_101,B_102] :
      ( ~ r2_hidden('#skF_7'(A_99,B_100,k3_setfam_1(A_99,B_100),'#skF_1'(A_101,B_102)),B_102)
      | r1_setfam_1(A_101,B_102)
      | ~ r2_hidden('#skF_1'(A_101,B_102),k3_setfam_1(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_80,c_6])).

tff(c_92,plain,(
    ! [A_103,A_104,B_105] :
      ( r1_setfam_1(A_103,A_104)
      | ~ r2_hidden('#skF_1'(A_103,A_104),k3_setfam_1(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_16,c_86])).

tff(c_97,plain,(
    ! [B_2,B_105] : r1_setfam_1(k3_setfam_1(B_2,B_105),B_2) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_36,plain,(
    ~ r1_setfam_1(k3_setfam_1('#skF_9','#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_36])).

%------------------------------------------------------------------------------
