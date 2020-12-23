%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0403+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:15 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  68 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1

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

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_setfam_1(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    ! [A_49] : r1_setfam_1(A_49,A_49) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [A_47] : k2_xboole_0(A_47,A_47) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58,plain,(
    ! [E_64,F_65,A_66,B_67] :
      ( r2_hidden(k2_xboole_0(E_64,F_65),k2_setfam_1(A_66,B_67))
      | ~ r2_hidden(F_65,B_67)
      | ~ r2_hidden(E_64,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_61,plain,(
    ! [A_47,A_66,B_67] :
      ( r2_hidden(A_47,k2_setfam_1(A_66,B_67))
      | ~ r2_hidden(A_47,B_67)
      | ~ r2_hidden(A_47,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_58])).

tff(c_4,plain,(
    ! [A_1,B_2,C_11] :
      ( r2_hidden('#skF_2'(A_1,B_2,C_11),B_2)
      | ~ r2_hidden(C_11,A_1)
      | ~ r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(C_61,'#skF_2'(A_62,B_63,C_61))
      | ~ r2_hidden(C_61,A_62)
      | ~ r1_setfam_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [A_1,B_2,D_10] :
      ( ~ r1_tarski('#skF_1'(A_1,B_2),D_10)
      | ~ r2_hidden(D_10,B_2)
      | r1_setfam_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    ! [A_86,B_87,A_88,B_89] :
      ( ~ r2_hidden('#skF_2'(A_86,B_87,'#skF_1'(A_88,B_89)),B_89)
      | r1_setfam_1(A_88,B_89)
      | ~ r2_hidden('#skF_1'(A_88,B_89),A_86)
      | ~ r1_setfam_1(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_52,c_6])).

tff(c_91,plain,(
    ! [A_93,B_94,A_95] :
      ( r1_setfam_1(A_93,B_94)
      | ~ r2_hidden('#skF_1'(A_93,B_94),A_95)
      | ~ r1_setfam_1(A_95,B_94) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_101,plain,(
    ! [A_96,B_97,A_98,B_99] :
      ( r1_setfam_1(A_96,B_97)
      | ~ r1_setfam_1(k2_setfam_1(A_98,B_99),B_97)
      | ~ r2_hidden('#skF_1'(A_96,B_97),B_99)
      | ~ r2_hidden('#skF_1'(A_96,B_97),A_98) ) ),
    inference(resolution,[status(thm)],[c_61,c_91])).

tff(c_106,plain,(
    ! [A_100,A_101,B_102] :
      ( r1_setfam_1(A_100,k2_setfam_1(A_101,B_102))
      | ~ r2_hidden('#skF_1'(A_100,k2_setfam_1(A_101,B_102)),B_102)
      | ~ r2_hidden('#skF_1'(A_100,k2_setfam_1(A_101,B_102)),A_101) ) ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_120,plain,(
    ! [A_108,A_109] :
      ( ~ r2_hidden('#skF_1'(A_108,k2_setfam_1(A_109,A_108)),A_109)
      | r1_setfam_1(A_108,k2_setfam_1(A_109,A_108)) ) ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_130,plain,(
    ! [A_1] : r1_setfam_1(A_1,k2_setfam_1(A_1,A_1)) ),
    inference(resolution,[status(thm)],[c_8,c_120])).

tff(c_38,plain,(
    ~ r1_setfam_1('#skF_9',k2_setfam_1('#skF_9','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_38])).

%------------------------------------------------------------------------------
