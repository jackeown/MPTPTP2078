%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:14 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   52 (  80 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :   48 (  77 expanded)
%              Number of equality atoms :   28 (  55 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_18,c_73])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_94])).

tff(c_112,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),k3_xboole_0(A_9,B_10)) = k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_113])).

tff(c_2145,plain,(
    ! [A_75,B_76] : k2_xboole_0(k4_xboole_0(A_75,B_76),k3_xboole_0(A_75,B_76)) = k2_xboole_0(A_75,k4_xboole_0(A_75,B_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k4_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)) = k4_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2151,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k4_xboole_0(B_76,B_76)) = k2_xboole_0(A_75,k4_xboole_0(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2145,c_16])).

tff(c_2220,plain,(
    ! [A_75,B_76] : k2_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_112,c_2151])).

tff(c_130,plain,(
    ! [A_33] : k4_xboole_0(A_33,A_33) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_138,plain,(
    ! [A_33] : k4_xboole_0(A_33,k1_xboole_0) = k3_xboole_0(A_33,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_12])).

tff(c_150,plain,(
    ! [A_33] : k3_xboole_0(A_33,A_33) = A_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138])).

tff(c_341,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k4_xboole_0(A_41,B_42),k3_xboole_0(A_41,C_43)) = k4_xboole_0(A_41,k4_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1093,plain,(
    ! [A_61,C_62,B_63] : k2_xboole_0(k3_xboole_0(A_61,C_62),k4_xboole_0(A_61,B_63)) = k4_xboole_0(A_61,k4_xboole_0(B_63,C_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_2])).

tff(c_1137,plain,(
    ! [A_33,B_63] : k4_xboole_0(A_33,k4_xboole_0(B_63,A_33)) = k2_xboole_0(A_33,k4_xboole_0(A_33,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_1093])).

tff(c_2808,plain,(
    ! [A_92,B_93] : k4_xboole_0(A_92,k4_xboole_0(B_93,A_92)) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2220,c_1137])).

tff(c_2856,plain,(
    ! [A_92,B_93] : k3_xboole_0(A_92,k4_xboole_0(B_93,A_92)) = k4_xboole_0(A_92,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_2808,c_12])).

tff(c_3014,plain,(
    ! [A_96,B_97] : k3_xboole_0(A_96,k4_xboole_0(B_97,A_96)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2856])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( ~ r1_xboole_0(k3_xboole_0(A_17,B_18),B_18)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3060,plain,(
    ! [B_97,A_96] :
      ( ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(B_97,A_96))
      | r1_xboole_0(A_96,k4_xboole_0(B_97,A_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3014,c_20])).

tff(c_3111,plain,(
    ! [A_98,B_99] : r1_xboole_0(A_98,k4_xboole_0(B_99,A_98)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3060])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3138,plain,(
    ! [B_99,A_98] : r1_xboole_0(k4_xboole_0(B_99,A_98),A_98) ),
    inference(resolution,[status(thm)],[c_3111,c_4])).

tff(c_22,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3138,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.55  
% 3.53/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.55  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.53/1.55  
% 3.53/1.55  %Foreground sorts:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Background operators:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Foreground operators:
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.53/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.55  
% 3.53/1.56  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.53/1.56  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.53/1.56  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.53/1.56  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.53/1.56  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.53/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.53/1.56  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.53/1.56  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.53/1.56  tff(f_51, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.53/1.56  tff(f_54, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.53/1.56  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.56  tff(c_73, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.56  tff(c_76, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_18, c_73])).
% 3.53/1.56  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.53/1.56  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.56  tff(c_94, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.56  tff(c_109, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_94])).
% 3.53/1.56  tff(c_112, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_109])).
% 3.53/1.56  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.53/1.56  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.56  tff(c_113, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.56  tff(c_122, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k3_xboole_0(A_9, B_10))=k2_xboole_0(k4_xboole_0(A_9, B_10), A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_113])).
% 3.53/1.56  tff(c_2145, plain, (![A_75, B_76]: (k2_xboole_0(k4_xboole_0(A_75, B_76), k3_xboole_0(A_75, B_76))=k2_xboole_0(A_75, k4_xboole_0(A_75, B_76)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_122])).
% 3.53/1.56  tff(c_16, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15))=k4_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.53/1.56  tff(c_2151, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k4_xboole_0(B_76, B_76))=k2_xboole_0(A_75, k4_xboole_0(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_2145, c_16])).
% 3.53/1.56  tff(c_2220, plain, (![A_75, B_76]: (k2_xboole_0(A_75, k4_xboole_0(A_75, B_76))=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_112, c_2151])).
% 3.53/1.56  tff(c_130, plain, (![A_33]: (k4_xboole_0(A_33, A_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_109])).
% 3.53/1.56  tff(c_138, plain, (![A_33]: (k4_xboole_0(A_33, k1_xboole_0)=k3_xboole_0(A_33, A_33))), inference(superposition, [status(thm), theory('equality')], [c_130, c_12])).
% 3.53/1.56  tff(c_150, plain, (![A_33]: (k3_xboole_0(A_33, A_33)=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138])).
% 3.53/1.56  tff(c_341, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k4_xboole_0(A_41, B_42), k3_xboole_0(A_41, C_43))=k4_xboole_0(A_41, k4_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.53/1.56  tff(c_1093, plain, (![A_61, C_62, B_63]: (k2_xboole_0(k3_xboole_0(A_61, C_62), k4_xboole_0(A_61, B_63))=k4_xboole_0(A_61, k4_xboole_0(B_63, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_341, c_2])).
% 3.53/1.56  tff(c_1137, plain, (![A_33, B_63]: (k4_xboole_0(A_33, k4_xboole_0(B_63, A_33))=k2_xboole_0(A_33, k4_xboole_0(A_33, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_1093])).
% 3.53/1.56  tff(c_2808, plain, (![A_92, B_93]: (k4_xboole_0(A_92, k4_xboole_0(B_93, A_92))=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_2220, c_1137])).
% 3.53/1.56  tff(c_2856, plain, (![A_92, B_93]: (k3_xboole_0(A_92, k4_xboole_0(B_93, A_92))=k4_xboole_0(A_92, A_92))), inference(superposition, [status(thm), theory('equality')], [c_2808, c_12])).
% 3.53/1.56  tff(c_3014, plain, (![A_96, B_97]: (k3_xboole_0(A_96, k4_xboole_0(B_97, A_96))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2856])).
% 3.53/1.56  tff(c_20, plain, (![A_17, B_18]: (~r1_xboole_0(k3_xboole_0(A_17, B_18), B_18) | r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.53/1.56  tff(c_3060, plain, (![B_97, A_96]: (~r1_xboole_0(k1_xboole_0, k4_xboole_0(B_97, A_96)) | r1_xboole_0(A_96, k4_xboole_0(B_97, A_96)))), inference(superposition, [status(thm), theory('equality')], [c_3014, c_20])).
% 3.53/1.56  tff(c_3111, plain, (![A_98, B_99]: (r1_xboole_0(A_98, k4_xboole_0(B_99, A_98)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3060])).
% 3.53/1.56  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.56  tff(c_3138, plain, (![B_99, A_98]: (r1_xboole_0(k4_xboole_0(B_99, A_98), A_98))), inference(resolution, [status(thm)], [c_3111, c_4])).
% 3.53/1.56  tff(c_22, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.53/1.56  tff(c_3144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3138, c_22])).
% 3.53/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.56  
% 3.53/1.56  Inference rules
% 3.53/1.56  ----------------------
% 3.53/1.56  #Ref     : 0
% 3.53/1.56  #Sup     : 700
% 3.53/1.56  #Fact    : 0
% 3.53/1.56  #Define  : 0
% 3.53/1.56  #Split   : 0
% 3.53/1.56  #Chain   : 0
% 3.53/1.56  #Close   : 0
% 3.53/1.56  
% 3.53/1.56  Ordering : KBO
% 3.53/1.56  
% 3.53/1.56  Simplification rules
% 3.53/1.56  ----------------------
% 3.53/1.56  #Subsume      : 12
% 3.53/1.56  #Demod        : 1029
% 3.53/1.56  #Tautology    : 545
% 3.53/1.56  #SimpNegUnit  : 0
% 3.53/1.56  #BackRed      : 26
% 3.53/1.56  
% 3.53/1.56  #Partial instantiations: 0
% 3.53/1.56  #Strategies tried      : 1
% 3.53/1.56  
% 3.53/1.56  Timing (in seconds)
% 3.53/1.56  ----------------------
% 3.53/1.56  Preprocessing        : 0.26
% 3.53/1.56  Parsing              : 0.15
% 3.53/1.56  CNF conversion       : 0.01
% 3.53/1.56  Main loop            : 0.55
% 3.53/1.56  Inferencing          : 0.18
% 3.53/1.56  Reduction            : 0.24
% 3.53/1.56  Demodulation         : 0.20
% 3.53/1.56  BG Simplification    : 0.02
% 3.53/1.57  Subsumption          : 0.07
% 3.53/1.57  Abstraction          : 0.03
% 3.53/1.57  MUC search           : 0.00
% 3.53/1.57  Cooper               : 0.00
% 3.53/1.57  Total                : 0.83
% 3.53/1.57  Index Insertion      : 0.00
% 3.53/1.57  Index Deletion       : 0.00
% 3.53/1.57  Index Matching       : 0.00
% 3.53/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
