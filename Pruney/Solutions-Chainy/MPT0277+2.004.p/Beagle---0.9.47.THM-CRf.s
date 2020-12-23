%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:20 EST 2020

% Result     : Theorem 22.10s
% Output     : CNFRefutation 22.10s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 683 expanded)
%              Number of leaves         :   32 ( 213 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 (1511 expanded)
%              Number of equality atoms :  219 (1437 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_30,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_204,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k2_xboole_0(A_74,B_75)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_220,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_204])).

tff(c_108,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_166,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_104,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_373,plain,(
    k1_tarski('#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_100,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k1_tarski('#skF_9') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_288,plain,(
    k1_tarski('#skF_9') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_96,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k2_tarski('#skF_8','#skF_9') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_495,plain,(
    k2_tarski('#skF_8','#skF_9') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_773,plain,(
    ! [A_113,B_114] : k2_xboole_0(k1_tarski(A_113),k1_tarski(B_114)) = k2_tarski(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1069,plain,(
    ! [B_133,A_134] : k2_xboole_0(k1_tarski(B_133),k1_tarski(A_134)) = k2_tarski(A_134,B_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_773])).

tff(c_56,plain,(
    ! [A_34,B_35] : k2_xboole_0(k1_tarski(A_34),k1_tarski(B_35)) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1081,plain,(
    ! [B_133,A_134] : k2_tarski(B_133,A_134) = k2_tarski(A_134,B_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_1069,c_56])).

tff(c_114,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1766,plain,
    ( k2_tarski('#skF_6','#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_114])).

tff(c_1767,plain,(
    k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1766])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4485,plain,(
    ! [B_247,C_248,A_249] :
      ( k2_tarski(B_247,C_248) = A_249
      | k1_tarski(C_248) = A_249
      | k1_tarski(B_247) = A_249
      | k1_xboole_0 = A_249
      | ~ r1_tarski(A_249,k2_tarski(B_247,C_248)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46357,plain,(
    ! [B_23534,C_23535,A_23536] :
      ( k2_tarski(B_23534,C_23535) = A_23536
      | k1_tarski(C_23535) = A_23536
      | k1_tarski(B_23534) = A_23536
      | k1_xboole_0 = A_23536
      | k4_xboole_0(A_23536,k2_tarski(B_23534,C_23535)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_4485])).

tff(c_46507,plain,
    ( k2_tarski('#skF_8','#skF_9') = '#skF_7'
    | k1_tarski('#skF_9') = '#skF_7'
    | k1_tarski('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_46357])).

tff(c_46567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_373,c_288,c_495,c_46507])).

tff(c_46568,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_6','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1766])).

tff(c_46603,plain,(
    k2_tarski('#skF_6','#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46568])).

tff(c_112,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_672,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_1124,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_672])).

tff(c_46604,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46603,c_1124])).

tff(c_46607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_46604])).

tff(c_46608,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46568])).

tff(c_46821,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46608])).

tff(c_30,plain,(
    ! [A_23] : k4_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46849,plain,(
    ! [A_23] : k4_xboole_0('#skF_4',A_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46821,c_46821,c_30])).

tff(c_46828,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46821,c_1124])).

tff(c_47180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46849,c_46828])).

tff(c_47181,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46608])).

tff(c_47183,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_47181])).

tff(c_82,plain,(
    ! [B_47,C_48] : r1_tarski(k1_tarski(B_47),k2_tarski(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_330,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k1_xboole_0
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_350,plain,(
    ! [B_47,C_48] : k4_xboole_0(k1_tarski(B_47),k2_tarski(B_47,C_48)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_330])).

tff(c_47242,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_tarski('#skF_6',C_48)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47183,c_350])).

tff(c_47687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47242,c_1124])).

tff(c_47688,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_47181])).

tff(c_80,plain,(
    ! [C_48,B_47] : r1_tarski(k1_tarski(C_48),k2_tarski(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_349,plain,(
    ! [C_48,B_47] : k4_xboole_0(k1_tarski(C_48),k2_tarski(B_47,C_48)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_330])).

tff(c_47751,plain,(
    ! [B_47] : k4_xboole_0('#skF_4',k2_tarski(B_47,'#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47688,c_349])).

tff(c_48283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47751,c_1124])).

tff(c_48284,plain,(
    k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_52680,plain,(
    ! [B_23822,C_23823,A_23824] :
      ( k2_tarski(B_23822,C_23823) = A_23824
      | k1_tarski(C_23823) = A_23824
      | k1_tarski(B_23822) = A_23824
      | k1_xboole_0 = A_23824
      | ~ r1_tarski(A_23824,k2_tarski(B_23822,C_23823)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_90386,plain,(
    ! [B_45348,C_45349,A_45350] :
      ( k2_tarski(B_45348,C_45349) = A_45350
      | k1_tarski(C_45349) = A_45350
      | k1_tarski(B_45348) = A_45350
      | k1_xboole_0 = A_45350
      | k4_xboole_0(A_45350,k2_tarski(B_45348,C_45349)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_52680])).

tff(c_90556,plain,
    ( k2_tarski('#skF_8','#skF_9') = '#skF_7'
    | k1_tarski('#skF_9') = '#skF_7'
    | k1_tarski('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_48284,c_90386])).

tff(c_90599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_373,c_288,c_495,c_90556])).

tff(c_90601,plain,(
    k2_tarski('#skF_8','#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_98,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k2_tarski('#skF_8','#skF_9') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_91019,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90601,c_98])).

tff(c_91020,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_91019])).

tff(c_91044,plain,(
    ! [A_23] : k4_xboole_0('#skF_4',A_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91020,c_91020,c_30])).

tff(c_90600,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_91027,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91020,c_90600])).

tff(c_91239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91044,c_91027])).

tff(c_91240,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_91019])).

tff(c_91679,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_91240])).

tff(c_91680,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91679,c_90600])).

tff(c_91683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_91680])).

tff(c_91684,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_91240])).

tff(c_91698,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_91684])).

tff(c_91730,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_tarski('#skF_5',C_48)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91698,c_350])).

tff(c_92389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91730,c_90600])).

tff(c_92390,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_91684])).

tff(c_92606,plain,(
    ! [B_45495] : r1_tarski('#skF_4',k2_tarski(B_45495,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92390,c_80])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92617,plain,(
    ! [B_45495] : k4_xboole_0('#skF_4',k2_tarski(B_45495,'#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92606,c_12])).

tff(c_93130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92617,c_90600])).

tff(c_93132,plain,(
    k1_tarski('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_106,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_93621,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93132,c_106])).

tff(c_93622,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_93621])).

tff(c_93645,plain,(
    ! [A_23] : k4_xboole_0('#skF_4',A_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93622,c_93622,c_30])).

tff(c_93131,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_93633,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93622,c_93131])).

tff(c_93879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93645,c_93633])).

tff(c_93880,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_93621])).

tff(c_94442,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_93880])).

tff(c_94443,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94442,c_93131])).

tff(c_94446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_94443])).

tff(c_94447,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_93880])).

tff(c_94461,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_94447])).

tff(c_94497,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_tarski('#skF_5',C_48)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94461,c_350])).

tff(c_94703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94497,c_93131])).

tff(c_94704,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_94447])).

tff(c_94818,plain,(
    ! [B_45599] : r1_tarski('#skF_4',k2_tarski(B_45599,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94704,c_80])).

tff(c_94829,plain,(
    ! [B_45599] : k4_xboole_0('#skF_4',k2_tarski(B_45599,'#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94818,c_12])).

tff(c_94928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94829,c_93131])).

tff(c_94930,plain,(
    k1_tarski('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_102,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_9') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_95750,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94930,c_102])).

tff(c_95751,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_95750])).

tff(c_95777,plain,(
    ! [A_23] : k4_xboole_0('#skF_4',A_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95751,c_95751,c_30])).

tff(c_94929,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_95768,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95751,c_94929])).

tff(c_96112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95777,c_95768])).

tff(c_96113,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_95750])).

tff(c_96731,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_96113])).

tff(c_96732,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96731,c_94929])).

tff(c_96735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_96732])).

tff(c_96736,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_96113])).

tff(c_96738,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_96736])).

tff(c_94990,plain,(
    ! [A_45613,B_45614] :
      ( k4_xboole_0(A_45613,B_45614) = k1_xboole_0
      | ~ r1_tarski(A_45613,B_45614) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_95017,plain,(
    ! [B_47,C_48] : k4_xboole_0(k1_tarski(B_47),k2_tarski(B_47,C_48)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_94990])).

tff(c_96777,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_tarski('#skF_5',C_48)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96738,c_95017])).

tff(c_97072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96777,c_94929])).

tff(c_97073,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_96736])).

tff(c_95016,plain,(
    ! [C_48,B_47] : k4_xboole_0(k1_tarski(C_48),k2_tarski(B_47,C_48)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_94990])).

tff(c_97110,plain,(
    ! [B_47] : k4_xboole_0('#skF_4',k2_tarski(B_47,'#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_97073,c_95016])).

tff(c_97412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97110,c_94929])).

tff(c_97414,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_24,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97507,plain,(
    ! [A_45732,B_45733] : k4_xboole_0(A_45732,k2_xboole_0(A_45732,B_45733)) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97414,c_24])).

tff(c_97526,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_97507])).

tff(c_97709,plain,(
    ! [A_45761,B_45762] : k2_xboole_0(k1_tarski(A_45761),k1_tarski(B_45762)) = k2_tarski(A_45761,B_45762) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_98898,plain,(
    ! [B_45824,A_45825] : k2_xboole_0(k1_tarski(B_45824),k1_tarski(A_45825)) = k2_tarski(A_45825,B_45824) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_97709])).

tff(c_98919,plain,(
    ! [B_45824,A_45825] : k2_tarski(B_45824,A_45825) = k2_tarski(A_45825,B_45824) ),
    inference(superposition,[status(thm),theory(equality)],[c_98898,c_56])).

tff(c_110,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_97889,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97414,c_97414,c_110])).

tff(c_97890,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_97889])).

tff(c_97418,plain,(
    ! [A_23] : k4_xboole_0('#skF_7',A_23) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97414,c_97414,c_30])).

tff(c_97908,plain,(
    ! [A_23] : k4_xboole_0('#skF_4',A_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97890,c_97890,c_97418])).

tff(c_97413,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_97472,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97414,c_97413])).

tff(c_97902,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97890,c_97472])).

tff(c_98067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97908,c_97902])).

tff(c_98068,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_97889])).

tff(c_99144,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_6','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98919,c_98068])).

tff(c_99145,plain,(
    k2_tarski('#skF_6','#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_99144])).

tff(c_98965,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98919,c_97472])).

tff(c_99146,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99145,c_98965])).

tff(c_99149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97526,c_99146])).

tff(c_99150,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_99144])).

tff(c_99152,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_99150])).

tff(c_97620,plain,(
    ! [A_45749,B_45750] :
      ( k4_xboole_0(A_45749,B_45750) = '#skF_7'
      | ~ r1_tarski(A_45749,B_45750) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97414,c_12])).

tff(c_97644,plain,(
    ! [C_48,B_47] : k4_xboole_0(k1_tarski(C_48),k2_tarski(B_47,C_48)) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_80,c_97620])).

tff(c_99199,plain,(
    ! [B_47] : k4_xboole_0('#skF_4',k2_tarski(B_47,'#skF_5')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_99152,c_97644])).

tff(c_99522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99199,c_98965])).

tff(c_99523,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_99150])).

tff(c_97643,plain,(
    ! [B_47,C_48] : k4_xboole_0(k1_tarski(B_47),k2_tarski(B_47,C_48)) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_82,c_97620])).

tff(c_99574,plain,(
    ! [C_48] : k4_xboole_0('#skF_4',k2_tarski('#skF_6',C_48)) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_99523,c_97643])).

tff(c_99922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99574,c_98965])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.10/11.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.10/11.34  
% 22.10/11.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.10/11.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 22.10/11.34  
% 22.10/11.34  %Foreground sorts:
% 22.10/11.34  
% 22.10/11.34  
% 22.10/11.34  %Background operators:
% 22.10/11.34  
% 22.10/11.34  
% 22.10/11.34  %Foreground operators:
% 22.10/11.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.10/11.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.10/11.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.10/11.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.10/11.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.10/11.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.10/11.34  tff('#skF_7', type, '#skF_7': $i).
% 22.10/11.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.10/11.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.10/11.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.10/11.34  tff('#skF_5', type, '#skF_5': $i).
% 22.10/11.34  tff('#skF_6', type, '#skF_6': $i).
% 22.10/11.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.10/11.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 22.10/11.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.10/11.34  tff('#skF_9', type, '#skF_9': $i).
% 22.10/11.34  tff('#skF_8', type, '#skF_8': $i).
% 22.10/11.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.10/11.34  tff('#skF_4', type, '#skF_4': $i).
% 22.10/11.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 22.10/11.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.10/11.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.10/11.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.10/11.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.10/11.34  
% 22.10/11.36  tff(f_30, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 22.10/11.36  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 22.10/11.36  tff(f_145, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 22.10/11.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 22.10/11.36  tff(f_81, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 22.10/11.36  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 22.10/11.36  tff(f_115, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 22.10/11.36  tff(f_62, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 22.10/11.36  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_30])).
% 22.10/11.36  tff(c_204, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k2_xboole_0(A_74, B_75))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 22.10/11.36  tff(c_220, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_204])).
% 22.10/11.36  tff(c_108, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_166, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_108])).
% 22.10/11.36  tff(c_104, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_373, plain, (k1_tarski('#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_104])).
% 22.10/11.36  tff(c_100, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_tarski('#skF_9')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_288, plain, (k1_tarski('#skF_9')!='#skF_7'), inference(splitLeft, [status(thm)], [c_100])).
% 22.10/11.36  tff(c_96, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k2_tarski('#skF_8', '#skF_9')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_495, plain, (k2_tarski('#skF_8', '#skF_9')!='#skF_7'), inference(splitLeft, [status(thm)], [c_96])).
% 22.10/11.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.10/11.36  tff(c_773, plain, (![A_113, B_114]: (k2_xboole_0(k1_tarski(A_113), k1_tarski(B_114))=k2_tarski(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.10/11.36  tff(c_1069, plain, (![B_133, A_134]: (k2_xboole_0(k1_tarski(B_133), k1_tarski(A_134))=k2_tarski(A_134, B_133))), inference(superposition, [status(thm), theory('equality')], [c_2, c_773])).
% 22.10/11.36  tff(c_56, plain, (![A_34, B_35]: (k2_xboole_0(k1_tarski(A_34), k1_tarski(B_35))=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.10/11.36  tff(c_1081, plain, (![B_133, A_134]: (k2_tarski(B_133, A_134)=k2_tarski(A_134, B_133))), inference(superposition, [status(thm), theory('equality')], [c_1069, c_56])).
% 22.10/11.36  tff(c_114, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_1766, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_114])).
% 22.10/11.36  tff(c_1767, plain, (k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1766])).
% 22.10/11.36  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.10/11.36  tff(c_4485, plain, (![B_247, C_248, A_249]: (k2_tarski(B_247, C_248)=A_249 | k1_tarski(C_248)=A_249 | k1_tarski(B_247)=A_249 | k1_xboole_0=A_249 | ~r1_tarski(A_249, k2_tarski(B_247, C_248)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.10/11.36  tff(c_46357, plain, (![B_23534, C_23535, A_23536]: (k2_tarski(B_23534, C_23535)=A_23536 | k1_tarski(C_23535)=A_23536 | k1_tarski(B_23534)=A_23536 | k1_xboole_0=A_23536 | k4_xboole_0(A_23536, k2_tarski(B_23534, C_23535))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_4485])).
% 22.10/11.36  tff(c_46507, plain, (k2_tarski('#skF_8', '#skF_9')='#skF_7' | k1_tarski('#skF_9')='#skF_7' | k1_tarski('#skF_8')='#skF_7' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1767, c_46357])).
% 22.10/11.36  tff(c_46567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_373, c_288, c_495, c_46507])).
% 22.10/11.36  tff(c_46568, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_6', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_1766])).
% 22.10/11.36  tff(c_46603, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_46568])).
% 22.10/11.36  tff(c_112, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_672, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_112])).
% 22.10/11.36  tff(c_1124, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_672])).
% 22.10/11.36  tff(c_46604, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46603, c_1124])).
% 22.10/11.36  tff(c_46607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_46604])).
% 22.10/11.36  tff(c_46608, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_46568])).
% 22.10/11.36  tff(c_46821, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_46608])).
% 22.10/11.36  tff(c_30, plain, (![A_23]: (k4_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.10/11.36  tff(c_46849, plain, (![A_23]: (k4_xboole_0('#skF_4', A_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46821, c_46821, c_30])).
% 22.10/11.36  tff(c_46828, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46821, c_1124])).
% 22.10/11.36  tff(c_47180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46849, c_46828])).
% 22.10/11.36  tff(c_47181, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_46608])).
% 22.10/11.36  tff(c_47183, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_47181])).
% 22.10/11.36  tff(c_82, plain, (![B_47, C_48]: (r1_tarski(k1_tarski(B_47), k2_tarski(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.10/11.36  tff(c_330, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k1_xboole_0 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.10/11.36  tff(c_350, plain, (![B_47, C_48]: (k4_xboole_0(k1_tarski(B_47), k2_tarski(B_47, C_48))=k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_330])).
% 22.10/11.36  tff(c_47242, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_tarski('#skF_6', C_48))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47183, c_350])).
% 22.10/11.36  tff(c_47687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47242, c_1124])).
% 22.10/11.36  tff(c_47688, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_47181])).
% 22.10/11.36  tff(c_80, plain, (![C_48, B_47]: (r1_tarski(k1_tarski(C_48), k2_tarski(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.10/11.36  tff(c_349, plain, (![C_48, B_47]: (k4_xboole_0(k1_tarski(C_48), k2_tarski(B_47, C_48))=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_330])).
% 22.10/11.36  tff(c_47751, plain, (![B_47]: (k4_xboole_0('#skF_4', k2_tarski(B_47, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47688, c_349])).
% 22.10/11.36  tff(c_48283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47751, c_1124])).
% 22.10/11.36  tff(c_48284, plain, (k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_112])).
% 22.10/11.36  tff(c_52680, plain, (![B_23822, C_23823, A_23824]: (k2_tarski(B_23822, C_23823)=A_23824 | k1_tarski(C_23823)=A_23824 | k1_tarski(B_23822)=A_23824 | k1_xboole_0=A_23824 | ~r1_tarski(A_23824, k2_tarski(B_23822, C_23823)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.10/11.36  tff(c_90386, plain, (![B_45348, C_45349, A_45350]: (k2_tarski(B_45348, C_45349)=A_45350 | k1_tarski(C_45349)=A_45350 | k1_tarski(B_45348)=A_45350 | k1_xboole_0=A_45350 | k4_xboole_0(A_45350, k2_tarski(B_45348, C_45349))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_52680])).
% 22.10/11.36  tff(c_90556, plain, (k2_tarski('#skF_8', '#skF_9')='#skF_7' | k1_tarski('#skF_9')='#skF_7' | k1_tarski('#skF_8')='#skF_7' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_48284, c_90386])).
% 22.10/11.36  tff(c_90599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_373, c_288, c_495, c_90556])).
% 22.10/11.36  tff(c_90601, plain, (k2_tarski('#skF_8', '#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_96])).
% 22.10/11.36  tff(c_98, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k2_tarski('#skF_8', '#skF_9')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_91019, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90601, c_98])).
% 22.10/11.36  tff(c_91020, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_91019])).
% 22.10/11.36  tff(c_91044, plain, (![A_23]: (k4_xboole_0('#skF_4', A_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91020, c_91020, c_30])).
% 22.10/11.36  tff(c_90600, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_96])).
% 22.10/11.36  tff(c_91027, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_91020, c_90600])).
% 22.10/11.36  tff(c_91239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91044, c_91027])).
% 22.10/11.36  tff(c_91240, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_91019])).
% 22.10/11.36  tff(c_91679, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_91240])).
% 22.10/11.36  tff(c_91680, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_91679, c_90600])).
% 22.10/11.36  tff(c_91683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_91680])).
% 22.10/11.36  tff(c_91684, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_91240])).
% 22.10/11.36  tff(c_91698, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_91684])).
% 22.10/11.36  tff(c_91730, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_tarski('#skF_5', C_48))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_91698, c_350])).
% 22.10/11.36  tff(c_92389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91730, c_90600])).
% 22.10/11.36  tff(c_92390, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_91684])).
% 22.10/11.36  tff(c_92606, plain, (![B_45495]: (r1_tarski('#skF_4', k2_tarski(B_45495, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_92390, c_80])).
% 22.10/11.36  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.10/11.36  tff(c_92617, plain, (![B_45495]: (k4_xboole_0('#skF_4', k2_tarski(B_45495, '#skF_6'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_92606, c_12])).
% 22.10/11.36  tff(c_93130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92617, c_90600])).
% 22.10/11.36  tff(c_93132, plain, (k1_tarski('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_104])).
% 22.10/11.36  tff(c_106, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_93621, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93132, c_106])).
% 22.10/11.36  tff(c_93622, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_93621])).
% 22.10/11.36  tff(c_93645, plain, (![A_23]: (k4_xboole_0('#skF_4', A_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93622, c_93622, c_30])).
% 22.10/11.36  tff(c_93131, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_104])).
% 22.10/11.36  tff(c_93633, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93622, c_93131])).
% 22.10/11.36  tff(c_93879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93645, c_93633])).
% 22.10/11.36  tff(c_93880, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_93621])).
% 22.10/11.36  tff(c_94442, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_93880])).
% 22.10/11.36  tff(c_94443, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94442, c_93131])).
% 22.10/11.36  tff(c_94446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_94443])).
% 22.10/11.36  tff(c_94447, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_93880])).
% 22.10/11.36  tff(c_94461, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_94447])).
% 22.10/11.36  tff(c_94497, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_tarski('#skF_5', C_48))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94461, c_350])).
% 22.10/11.36  tff(c_94703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94497, c_93131])).
% 22.10/11.36  tff(c_94704, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_94447])).
% 22.10/11.36  tff(c_94818, plain, (![B_45599]: (r1_tarski('#skF_4', k2_tarski(B_45599, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_94704, c_80])).
% 22.10/11.36  tff(c_94829, plain, (![B_45599]: (k4_xboole_0('#skF_4', k2_tarski(B_45599, '#skF_6'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_94818, c_12])).
% 22.10/11.36  tff(c_94928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94829, c_93131])).
% 22.10/11.36  tff(c_94930, plain, (k1_tarski('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_100])).
% 22.10/11.36  tff(c_102, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k1_tarski('#skF_9')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_95750, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94930, c_102])).
% 22.10/11.36  tff(c_95751, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_95750])).
% 22.10/11.36  tff(c_95777, plain, (![A_23]: (k4_xboole_0('#skF_4', A_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_95751, c_95751, c_30])).
% 22.10/11.36  tff(c_94929, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_100])).
% 22.10/11.36  tff(c_95768, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_95751, c_94929])).
% 22.10/11.36  tff(c_96112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95777, c_95768])).
% 22.10/11.36  tff(c_96113, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_95750])).
% 22.10/11.36  tff(c_96731, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_96113])).
% 22.10/11.36  tff(c_96732, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_96731, c_94929])).
% 22.10/11.36  tff(c_96735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_96732])).
% 22.10/11.36  tff(c_96736, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_96113])).
% 22.10/11.36  tff(c_96738, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_96736])).
% 22.10/11.36  tff(c_94990, plain, (![A_45613, B_45614]: (k4_xboole_0(A_45613, B_45614)=k1_xboole_0 | ~r1_tarski(A_45613, B_45614))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.10/11.36  tff(c_95017, plain, (![B_47, C_48]: (k4_xboole_0(k1_tarski(B_47), k2_tarski(B_47, C_48))=k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_94990])).
% 22.10/11.36  tff(c_96777, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_tarski('#skF_5', C_48))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96738, c_95017])).
% 22.10/11.36  tff(c_97072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96777, c_94929])).
% 22.10/11.36  tff(c_97073, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_96736])).
% 22.10/11.36  tff(c_95016, plain, (![C_48, B_47]: (k4_xboole_0(k1_tarski(C_48), k2_tarski(B_47, C_48))=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_94990])).
% 22.10/11.36  tff(c_97110, plain, (![B_47]: (k4_xboole_0('#skF_4', k2_tarski(B_47, '#skF_6'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_97073, c_95016])).
% 22.10/11.36  tff(c_97412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97110, c_94929])).
% 22.10/11.36  tff(c_97414, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_108])).
% 22.10/11.36  tff(c_24, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 22.10/11.36  tff(c_97507, plain, (![A_45732, B_45733]: (k4_xboole_0(A_45732, k2_xboole_0(A_45732, B_45733))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_97414, c_24])).
% 22.10/11.36  tff(c_97526, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6, c_97507])).
% 22.10/11.36  tff(c_97709, plain, (![A_45761, B_45762]: (k2_xboole_0(k1_tarski(A_45761), k1_tarski(B_45762))=k2_tarski(A_45761, B_45762))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.10/11.36  tff(c_98898, plain, (![B_45824, A_45825]: (k2_xboole_0(k1_tarski(B_45824), k1_tarski(A_45825))=k2_tarski(A_45825, B_45824))), inference(superposition, [status(thm), theory('equality')], [c_2, c_97709])).
% 22.10/11.36  tff(c_98919, plain, (![B_45824, A_45825]: (k2_tarski(B_45824, A_45825)=k2_tarski(A_45825, B_45824))), inference(superposition, [status(thm), theory('equality')], [c_98898, c_56])).
% 22.10/11.36  tff(c_110, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.10/11.36  tff(c_97889, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97414, c_97414, c_110])).
% 22.10/11.36  tff(c_97890, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_97889])).
% 22.10/11.36  tff(c_97418, plain, (![A_23]: (k4_xboole_0('#skF_7', A_23)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_97414, c_97414, c_30])).
% 22.10/11.36  tff(c_97908, plain, (![A_23]: (k4_xboole_0('#skF_4', A_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97890, c_97890, c_97418])).
% 22.10/11.36  tff(c_97413, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_108])).
% 22.10/11.36  tff(c_97472, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_97414, c_97413])).
% 22.10/11.36  tff(c_97902, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97890, c_97472])).
% 22.10/11.36  tff(c_98067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97908, c_97902])).
% 22.10/11.36  tff(c_98068, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_97889])).
% 22.10/11.36  tff(c_99144, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_6', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_98919, c_98068])).
% 22.10/11.36  tff(c_99145, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_99144])).
% 22.10/11.36  tff(c_98965, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_98919, c_97472])).
% 22.10/11.36  tff(c_99146, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_99145, c_98965])).
% 22.10/11.36  tff(c_99149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97526, c_99146])).
% 22.10/11.36  tff(c_99150, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_99144])).
% 22.10/11.36  tff(c_99152, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_99150])).
% 22.10/11.36  tff(c_97620, plain, (![A_45749, B_45750]: (k4_xboole_0(A_45749, B_45750)='#skF_7' | ~r1_tarski(A_45749, B_45750))), inference(demodulation, [status(thm), theory('equality')], [c_97414, c_12])).
% 22.10/11.36  tff(c_97644, plain, (![C_48, B_47]: (k4_xboole_0(k1_tarski(C_48), k2_tarski(B_47, C_48))='#skF_7')), inference(resolution, [status(thm)], [c_80, c_97620])).
% 22.10/11.36  tff(c_99199, plain, (![B_47]: (k4_xboole_0('#skF_4', k2_tarski(B_47, '#skF_5'))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_99152, c_97644])).
% 22.10/11.36  tff(c_99522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99199, c_98965])).
% 22.10/11.36  tff(c_99523, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_99150])).
% 22.10/11.36  tff(c_97643, plain, (![B_47, C_48]: (k4_xboole_0(k1_tarski(B_47), k2_tarski(B_47, C_48))='#skF_7')), inference(resolution, [status(thm)], [c_82, c_97620])).
% 22.10/11.36  tff(c_99574, plain, (![C_48]: (k4_xboole_0('#skF_4', k2_tarski('#skF_6', C_48))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_99523, c_97643])).
% 22.10/11.36  tff(c_99922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99574, c_98965])).
% 22.10/11.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.10/11.36  
% 22.10/11.36  Inference rules
% 22.10/11.36  ----------------------
% 22.10/11.36  #Ref     : 0
% 22.10/11.36  #Sup     : 18617
% 22.10/11.36  #Fact    : 82
% 22.10/11.36  #Define  : 0
% 22.10/11.36  #Split   : 87
% 22.10/11.36  #Chain   : 0
% 22.10/11.36  #Close   : 0
% 22.10/11.36  
% 22.10/11.36  Ordering : KBO
% 22.10/11.36  
% 22.10/11.36  Simplification rules
% 22.10/11.36  ----------------------
% 22.10/11.36  #Subsume      : 4074
% 22.10/11.36  #Demod        : 17875
% 22.10/11.36  #Tautology    : 8174
% 22.10/11.36  #SimpNegUnit  : 1175
% 22.10/11.36  #BackRed      : 165
% 22.10/11.36  
% 22.10/11.36  #Partial instantiations: 31365
% 22.10/11.36  #Strategies tried      : 1
% 22.10/11.36  
% 22.10/11.36  Timing (in seconds)
% 22.10/11.36  ----------------------
% 22.10/11.36  Preprocessing        : 0.36
% 22.10/11.36  Parsing              : 0.18
% 22.10/11.36  CNF conversion       : 0.03
% 22.10/11.36  Main loop            : 10.22
% 22.10/11.36  Inferencing          : 2.53
% 22.10/11.36  Reduction            : 5.04
% 22.10/11.36  Demodulation         : 4.22
% 22.10/11.36  BG Simplification    : 0.25
% 22.10/11.36  Subsumption          : 1.95
% 22.10/11.36  Abstraction          : 0.40
% 22.10/11.36  MUC search           : 0.00
% 22.10/11.36  Cooper               : 0.00
% 22.10/11.36  Total                : 10.63
% 22.10/11.37  Index Insertion      : 0.00
% 22.10/11.37  Index Deletion       : 0.00
% 22.10/11.37  Index Matching       : 0.00
% 22.10/11.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
