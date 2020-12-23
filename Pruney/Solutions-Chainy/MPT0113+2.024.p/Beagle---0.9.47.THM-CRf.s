%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:14 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 108 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :   84 ( 137 expanded)
%              Number of equality atoms :   46 (  67 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_157,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | k4_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_161,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_157,c_73])).

tff(c_40,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ! [A_28,B_29] : r1_xboole_0(k4_xboole_0(A_28,B_29),B_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_442,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_xboole_0(A_71,C_72)
      | ~ r1_xboole_0(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1006,plain,(
    ! [A_106,B_107,A_108] :
      ( r1_xboole_0(A_106,B_107)
      | ~ r1_tarski(A_106,k4_xboole_0(A_108,B_107)) ) ),
    inference(resolution,[status(thm)],[c_32,c_442])).

tff(c_1027,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1006])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1034,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1027,c_4])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k4_xboole_0(A_22,B_23),k3_xboole_0(A_22,C_24)) = k4_xboole_0(A_22,k4_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1657,plain,(
    ! [B_139] : k4_xboole_0('#skF_2',k4_xboole_0(B_139,'#skF_4')) = k2_xboole_0(k4_xboole_0('#skF_2',B_139),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_28])).

tff(c_162,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_170,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_162])).

tff(c_26,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    k4_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_26])).

tff(c_1687,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_228])).

tff(c_24,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_331,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_355,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = k4_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_331])).

tff(c_358,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_355])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_45] : k3_xboole_0(k1_xboole_0,A_45) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_20])).

tff(c_346,plain,(
    ! [A_45] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_331])).

tff(c_369,plain,(
    ! [A_66] : k4_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_346])).

tff(c_386,plain,(
    ! [A_66] : r1_xboole_0(k1_xboole_0,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_32])).

tff(c_505,plain,(
    ! [A_78,A_79] :
      ( r1_xboole_0(A_78,A_79)
      | ~ r1_tarski(A_78,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_386,c_442])).

tff(c_513,plain,(
    ! [A_80,A_81] :
      ( k3_xboole_0(A_80,A_81) = k1_xboole_0
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_505,c_4])).

tff(c_516,plain,(
    ! [A_10,A_81] :
      ( k3_xboole_0(A_10,A_81) = k1_xboole_0
      | k4_xboole_0(A_10,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_513])).

tff(c_521,plain,(
    ! [A_82,A_83] :
      ( k3_xboole_0(A_82,A_83) = k1_xboole_0
      | k1_xboole_0 != A_82 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_516])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_777,plain,(
    ! [A_97,A_98] :
      ( k3_xboole_0(A_97,A_98) = k1_xboole_0
      | k1_xboole_0 != A_98 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_2])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_792,plain,(
    ! [A_97,A_98] :
      ( k5_xboole_0(A_97,k1_xboole_0) = k4_xboole_0(A_97,A_98)
      | k1_xboole_0 != A_98 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_777,c_16])).

tff(c_861,plain,(
    ! [A_99,A_100] :
      ( k4_xboole_0(A_99,A_100) = A_99
      | k1_xboole_0 != A_100 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_792])).

tff(c_922,plain,(
    ! [A_20,B_21] :
      ( k1_xboole_0 = A_20
      | k2_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_861])).

tff(c_1725,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1687,c_922])).

tff(c_1746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_1725])).

tff(c_1747,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2160,plain,(
    ! [A_168,C_169,B_170] :
      ( r1_xboole_0(A_168,C_169)
      | ~ r1_xboole_0(B_170,C_169)
      | ~ r1_tarski(A_168,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2919,plain,(
    ! [A_205,B_206,A_207] :
      ( r1_xboole_0(A_205,B_206)
      | ~ r1_tarski(A_205,k4_xboole_0(A_207,B_206)) ) ),
    inference(resolution,[status(thm)],[c_32,c_2160])).

tff(c_2944,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2919])).

tff(c_2949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1747,c_2944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.72  
% 4.00/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.00/1.73  
% 4.00/1.73  %Foreground sorts:
% 4.00/1.73  
% 4.00/1.73  
% 4.00/1.73  %Background operators:
% 4.00/1.73  
% 4.00/1.73  
% 4.00/1.73  %Foreground operators:
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.00/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.00/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.00/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.00/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.00/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.00/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.00/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.00/1.73  
% 4.00/1.74  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.00/1.74  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.00/1.74  tff(f_73, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.00/1.74  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.00/1.74  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.00/1.74  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.00/1.74  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.00/1.74  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.00/1.74  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.00/1.74  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.00/1.74  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.00/1.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.00/1.74  tff(c_157, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | k4_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.00/1.74  tff(c_38, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.00/1.74  tff(c_73, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 4.00/1.74  tff(c_161, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_157, c_73])).
% 4.00/1.74  tff(c_40, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.00/1.74  tff(c_32, plain, (![A_28, B_29]: (r1_xboole_0(k4_xboole_0(A_28, B_29), B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.00/1.74  tff(c_442, plain, (![A_71, C_72, B_73]: (r1_xboole_0(A_71, C_72) | ~r1_xboole_0(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.00/1.74  tff(c_1006, plain, (![A_106, B_107, A_108]: (r1_xboole_0(A_106, B_107) | ~r1_tarski(A_106, k4_xboole_0(A_108, B_107)))), inference(resolution, [status(thm)], [c_32, c_442])).
% 4.00/1.74  tff(c_1027, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_1006])).
% 4.00/1.74  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.74  tff(c_1034, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1027, c_4])).
% 4.00/1.74  tff(c_28, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k4_xboole_0(A_22, B_23), k3_xboole_0(A_22, C_24))=k4_xboole_0(A_22, k4_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.00/1.74  tff(c_1657, plain, (![B_139]: (k4_xboole_0('#skF_2', k4_xboole_0(B_139, '#skF_4'))=k2_xboole_0(k4_xboole_0('#skF_2', B_139), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1034, c_28])).
% 4.00/1.74  tff(c_162, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.00/1.74  tff(c_170, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_162])).
% 4.00/1.74  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.00/1.74  tff(c_228, plain, (k4_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_170, c_26])).
% 4.00/1.74  tff(c_1687, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1657, c_228])).
% 4.00/1.74  tff(c_24, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.00/1.74  tff(c_20, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.00/1.74  tff(c_331, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.00/1.74  tff(c_355, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=k4_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_331])).
% 4.00/1.74  tff(c_358, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_355])).
% 4.00/1.74  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.00/1.74  tff(c_74, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.00/1.74  tff(c_90, plain, (![A_45]: (k3_xboole_0(k1_xboole_0, A_45)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_20])).
% 4.00/1.74  tff(c_346, plain, (![A_45]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_45))), inference(superposition, [status(thm), theory('equality')], [c_90, c_331])).
% 4.00/1.74  tff(c_369, plain, (![A_66]: (k4_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_358, c_346])).
% 4.00/1.74  tff(c_386, plain, (![A_66]: (r1_xboole_0(k1_xboole_0, A_66))), inference(superposition, [status(thm), theory('equality')], [c_369, c_32])).
% 4.00/1.74  tff(c_505, plain, (![A_78, A_79]: (r1_xboole_0(A_78, A_79) | ~r1_tarski(A_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_386, c_442])).
% 4.00/1.74  tff(c_513, plain, (![A_80, A_81]: (k3_xboole_0(A_80, A_81)=k1_xboole_0 | ~r1_tarski(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_505, c_4])).
% 4.00/1.74  tff(c_516, plain, (![A_10, A_81]: (k3_xboole_0(A_10, A_81)=k1_xboole_0 | k4_xboole_0(A_10, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_513])).
% 4.00/1.74  tff(c_521, plain, (![A_82, A_83]: (k3_xboole_0(A_82, A_83)=k1_xboole_0 | k1_xboole_0!=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_516])).
% 4.00/1.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.00/1.74  tff(c_777, plain, (![A_97, A_98]: (k3_xboole_0(A_97, A_98)=k1_xboole_0 | k1_xboole_0!=A_98)), inference(superposition, [status(thm), theory('equality')], [c_521, c_2])).
% 4.00/1.74  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.00/1.74  tff(c_792, plain, (![A_97, A_98]: (k5_xboole_0(A_97, k1_xboole_0)=k4_xboole_0(A_97, A_98) | k1_xboole_0!=A_98)), inference(superposition, [status(thm), theory('equality')], [c_777, c_16])).
% 4.00/1.74  tff(c_861, plain, (![A_99, A_100]: (k4_xboole_0(A_99, A_100)=A_99 | k1_xboole_0!=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_358, c_792])).
% 4.00/1.74  tff(c_922, plain, (![A_20, B_21]: (k1_xboole_0=A_20 | k2_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_861])).
% 4.00/1.74  tff(c_1725, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1687, c_922])).
% 4.00/1.74  tff(c_1746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_1725])).
% 4.00/1.74  tff(c_1747, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 4.00/1.74  tff(c_2160, plain, (![A_168, C_169, B_170]: (r1_xboole_0(A_168, C_169) | ~r1_xboole_0(B_170, C_169) | ~r1_tarski(A_168, B_170))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.00/1.74  tff(c_2919, plain, (![A_205, B_206, A_207]: (r1_xboole_0(A_205, B_206) | ~r1_tarski(A_205, k4_xboole_0(A_207, B_206)))), inference(resolution, [status(thm)], [c_32, c_2160])).
% 4.00/1.74  tff(c_2944, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_2919])).
% 4.00/1.74  tff(c_2949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1747, c_2944])).
% 4.00/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.74  
% 4.00/1.74  Inference rules
% 4.00/1.74  ----------------------
% 4.00/1.74  #Ref     : 0
% 4.00/1.74  #Sup     : 762
% 4.00/1.74  #Fact    : 0
% 4.00/1.74  #Define  : 0
% 4.00/1.74  #Split   : 2
% 4.00/1.74  #Chain   : 0
% 4.00/1.74  #Close   : 0
% 4.00/1.74  
% 4.00/1.74  Ordering : KBO
% 4.00/1.74  
% 4.00/1.74  Simplification rules
% 4.00/1.74  ----------------------
% 4.00/1.74  #Subsume      : 144
% 4.00/1.74  #Demod        : 249
% 4.00/1.74  #Tautology    : 378
% 4.00/1.74  #SimpNegUnit  : 33
% 4.00/1.74  #BackRed      : 0
% 4.00/1.74  
% 4.00/1.74  #Partial instantiations: 0
% 4.00/1.74  #Strategies tried      : 1
% 4.00/1.74  
% 4.00/1.74  Timing (in seconds)
% 4.00/1.74  ----------------------
% 4.00/1.74  Preprocessing        : 0.32
% 4.00/1.74  Parsing              : 0.18
% 4.00/1.74  CNF conversion       : 0.02
% 4.00/1.74  Main loop            : 0.63
% 4.00/1.74  Inferencing          : 0.22
% 4.00/1.74  Reduction            : 0.23
% 4.00/1.74  Demodulation         : 0.17
% 4.00/1.74  BG Simplification    : 0.03
% 4.00/1.74  Subsumption          : 0.10
% 4.00/1.74  Abstraction          : 0.03
% 4.00/1.74  MUC search           : 0.00
% 4.00/1.74  Cooper               : 0.00
% 4.00/1.74  Total                : 0.98
% 4.00/1.74  Index Insertion      : 0.00
% 4.00/1.74  Index Deletion       : 0.00
% 4.00/1.74  Index Matching       : 0.00
% 4.00/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
