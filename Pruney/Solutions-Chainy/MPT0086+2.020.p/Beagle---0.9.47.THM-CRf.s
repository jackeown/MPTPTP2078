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
% DateTime   : Thu Dec  3 09:44:16 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 112 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 119 expanded)
%              Number of equality atoms :   36 (  80 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_52])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_149,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_131])).

tff(c_152,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_149])).

tff(c_162,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_149])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_167,plain,(
    ! [A_44] : k4_xboole_0(A_44,k1_xboole_0) = k3_xboole_0(A_44,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_16])).

tff(c_202,plain,(
    ! [A_47] : k3_xboole_0(A_47,A_47) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_20,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_211,plain,(
    ! [A_47] : k2_xboole_0(A_47,k4_xboole_0(A_47,A_47)) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_20])).

tff(c_235,plain,(
    ! [A_47] : k2_xboole_0(A_47,k1_xboole_0) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_211])).

tff(c_35,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_21] : r1_xboole_0(k1_xboole_0,A_21) ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_63,plain,(
    ! [A_21] : k3_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_111,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(A_39,B_40),k4_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_347,plain,(
    ! [A_56] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_56)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_111])).

tff(c_126,plain,(
    ! [A_10] : k2_xboole_0(k3_xboole_0(A_10,k1_xboole_0),A_10) = A_10 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_130,plain,(
    ! [A_10] : k2_xboole_0(k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_126])).

tff(c_352,plain,(
    ! [A_56] : k4_xboole_0(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_130])).

tff(c_286,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k4_xboole_0(A_53,B_54),C_55) = k4_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_319,plain,(
    ! [A_10,C_55] : k4_xboole_0(A_10,k2_xboole_0(A_10,C_55)) = k4_xboole_0(k1_xboole_0,C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_286])).

tff(c_798,plain,(
    ! [A_73,C_74] : k4_xboole_0(A_73,k2_xboole_0(A_73,C_74)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_319])).

tff(c_921,plain,(
    ! [A_77,B_78] : k4_xboole_0(k3_xboole_0(A_77,B_78),A_77) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_798])).

tff(c_323,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(B_54,k4_xboole_0(A_53,B_54))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_286])).

tff(c_926,plain,(
    ! [A_77,B_78] : k4_xboole_0(k3_xboole_0(A_77,B_78),k2_xboole_0(A_77,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_323])).

tff(c_969,plain,(
    ! [A_77,B_78] : k3_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_235,c_926])).

tff(c_44,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | k3_xboole_0(A_38,B_37) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_6])).

tff(c_24,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_110,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_24])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:43:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.33  
% 2.57/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.33  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.33  
% 2.57/1.33  %Foreground sorts:
% 2.57/1.33  
% 2.57/1.33  
% 2.57/1.33  %Background operators:
% 2.57/1.33  
% 2.57/1.33  
% 2.57/1.33  %Foreground operators:
% 2.57/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.33  
% 2.57/1.34  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.57/1.34  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.57/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.57/1.34  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.57/1.34  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.57/1.34  tff(f_57, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.57/1.34  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.57/1.34  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.57/1.34  tff(f_62, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.57/1.34  tff(c_18, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.34  tff(c_22, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.34  tff(c_52, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.34  tff(c_64, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_52])).
% 2.57/1.34  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.34  tff(c_131, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.34  tff(c_149, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_131])).
% 2.57/1.34  tff(c_152, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_149])).
% 2.57/1.34  tff(c_162, plain, (![A_44]: (k4_xboole_0(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_149])).
% 2.57/1.34  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.34  tff(c_167, plain, (![A_44]: (k4_xboole_0(A_44, k1_xboole_0)=k3_xboole_0(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_162, c_16])).
% 2.57/1.34  tff(c_202, plain, (![A_47]: (k3_xboole_0(A_47, A_47)=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_167])).
% 2.57/1.34  tff(c_20, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.34  tff(c_211, plain, (![A_47]: (k2_xboole_0(A_47, k4_xboole_0(A_47, A_47))=A_47)), inference(superposition, [status(thm), theory('equality')], [c_202, c_20])).
% 2.57/1.34  tff(c_235, plain, (![A_47]: (k2_xboole_0(A_47, k1_xboole_0)=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_211])).
% 2.57/1.34  tff(c_35, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.34  tff(c_38, plain, (![A_21]: (r1_xboole_0(k1_xboole_0, A_21))), inference(resolution, [status(thm)], [c_22, c_35])).
% 2.57/1.34  tff(c_63, plain, (![A_21]: (k3_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_52])).
% 2.57/1.34  tff(c_111, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(A_39, B_40), k4_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.34  tff(c_347, plain, (![A_56]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_56))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63, c_111])).
% 2.57/1.34  tff(c_126, plain, (![A_10]: (k2_xboole_0(k3_xboole_0(A_10, k1_xboole_0), A_10)=A_10)), inference(superposition, [status(thm), theory('equality')], [c_12, c_111])).
% 2.57/1.34  tff(c_130, plain, (![A_10]: (k2_xboole_0(k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_126])).
% 2.57/1.34  tff(c_352, plain, (![A_56]: (k4_xboole_0(k1_xboole_0, A_56)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_347, c_130])).
% 2.57/1.34  tff(c_286, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k4_xboole_0(A_53, B_54), C_55)=k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.34  tff(c_319, plain, (![A_10, C_55]: (k4_xboole_0(A_10, k2_xboole_0(A_10, C_55))=k4_xboole_0(k1_xboole_0, C_55))), inference(superposition, [status(thm), theory('equality')], [c_152, c_286])).
% 2.57/1.34  tff(c_798, plain, (![A_73, C_74]: (k4_xboole_0(A_73, k2_xboole_0(A_73, C_74))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_352, c_319])).
% 2.57/1.34  tff(c_921, plain, (![A_77, B_78]: (k4_xboole_0(k3_xboole_0(A_77, B_78), A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_798])).
% 2.57/1.34  tff(c_323, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(B_54, k4_xboole_0(A_53, B_54)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_286])).
% 2.57/1.34  tff(c_926, plain, (![A_77, B_78]: (k4_xboole_0(k3_xboole_0(A_77, B_78), k2_xboole_0(A_77, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_921, c_323])).
% 2.57/1.34  tff(c_969, plain, (![A_77, B_78]: (k3_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_235, c_926])).
% 2.57/1.34  tff(c_44, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.34  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.34  tff(c_99, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | k3_xboole_0(A_38, B_37)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_6])).
% 2.57/1.34  tff(c_24, plain, (~r1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.57/1.34  tff(c_110, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_24])).
% 2.57/1.34  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_969, c_110])).
% 2.57/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.34  
% 2.57/1.34  Inference rules
% 2.57/1.34  ----------------------
% 2.57/1.34  #Ref     : 0
% 2.57/1.34  #Sup     : 232
% 2.57/1.34  #Fact    : 0
% 2.57/1.34  #Define  : 0
% 2.57/1.34  #Split   : 0
% 2.57/1.34  #Chain   : 0
% 2.57/1.34  #Close   : 0
% 2.57/1.34  
% 2.57/1.34  Ordering : KBO
% 2.57/1.34  
% 2.57/1.34  Simplification rules
% 2.57/1.34  ----------------------
% 2.57/1.34  #Subsume      : 7
% 2.57/1.34  #Demod        : 158
% 2.57/1.34  #Tautology    : 138
% 2.57/1.34  #SimpNegUnit  : 3
% 2.57/1.34  #BackRed      : 2
% 2.57/1.34  
% 2.57/1.34  #Partial instantiations: 0
% 2.57/1.34  #Strategies tried      : 1
% 2.57/1.34  
% 2.57/1.34  Timing (in seconds)
% 2.57/1.34  ----------------------
% 2.57/1.34  Preprocessing        : 0.28
% 2.57/1.34  Parsing              : 0.15
% 2.57/1.34  CNF conversion       : 0.02
% 2.57/1.34  Main loop            : 0.30
% 2.57/1.34  Inferencing          : 0.12
% 2.57/1.34  Reduction            : 0.11
% 2.57/1.34  Demodulation         : 0.08
% 2.57/1.34  BG Simplification    : 0.01
% 2.57/1.34  Subsumption          : 0.04
% 2.57/1.34  Abstraction          : 0.02
% 2.57/1.34  MUC search           : 0.00
% 2.57/1.34  Cooper               : 0.00
% 2.57/1.34  Total                : 0.61
% 2.57/1.35  Index Insertion      : 0.00
% 2.57/1.35  Index Deletion       : 0.00
% 2.57/1.35  Index Matching       : 0.00
% 2.57/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
