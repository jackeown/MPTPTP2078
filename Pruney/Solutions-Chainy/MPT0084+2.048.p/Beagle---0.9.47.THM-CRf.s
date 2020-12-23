%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:10 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  75 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  88 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_68,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_173,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,k3_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_207,plain,(
    ! [A_48,B_49] :
      ( ~ r1_xboole_0(A_48,B_49)
      | k3_xboole_0(A_48,B_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_173])).

tff(c_222,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_207])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_357,plain,(
    k4_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_18])).

tff(c_364,plain,(
    k4_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_357])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_537,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k3_xboole_0(A_60,B_61),k3_xboole_0(A_60,C_62)) = k3_xboole_0(A_60,k4_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1586,plain,(
    ! [A_82,B_83,C_84] : k3_xboole_0(A_82,k4_xboole_0(B_83,k3_xboole_0(A_82,C_84))) = k3_xboole_0(A_82,k4_xboole_0(B_83,C_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_537])).

tff(c_1717,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_5')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_1586])).

tff(c_1784,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_76,c_1717])).

tff(c_26,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_186,plain,(
    ! [A_12,C_44] :
      ( ~ r1_xboole_0(A_12,k1_xboole_0)
      | ~ r2_hidden(C_44,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_173])).

tff(c_189,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_186])).

tff(c_455,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(A_57,k4_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_81])).

tff(c_103,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_622,plain,(
    ! [A_63,B_64] : k3_xboole_0(A_63,k4_xboole_0(B_64,k3_xboole_0(A_63,B_64))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_103])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_642,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,k4_xboole_0(B_64,k3_xboole_0(A_63,B_64))),k1_xboole_0)
      | r1_xboole_0(A_63,k4_xboole_0(B_64,k3_xboole_0(A_63,B_64))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_4])).

tff(c_874,plain,(
    ! [A_66,B_67] : r1_xboole_0(A_66,k4_xboole_0(B_67,k3_xboole_0(A_66,B_67))) ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_642])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_930,plain,(
    ! [B_67,A_66] : r1_xboole_0(k4_xboole_0(B_67,k3_xboole_0(A_66,B_67)),A_66) ),
    inference(resolution,[status(thm)],[c_874,c_2])).

tff(c_1800,plain,(
    r1_xboole_0(k4_xboole_0('#skF_3',k1_xboole_0),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1784,c_930])).

tff(c_1831,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1800])).

tff(c_1833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1831])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.64  
% 3.22/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.65  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.22/1.65  
% 3.22/1.65  %Foreground sorts:
% 3.22/1.65  
% 3.22/1.65  
% 3.22/1.65  %Background operators:
% 3.22/1.65  
% 3.22/1.65  
% 3.22/1.65  %Foreground operators:
% 3.22/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.22/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.22/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.65  
% 3.22/1.66  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.22/1.66  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.22/1.66  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.22/1.66  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.22/1.66  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.22/1.66  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.22/1.66  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.22/1.66  tff(f_65, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.22/1.66  tff(f_67, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 3.22/1.66  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.22/1.66  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.22/1.66  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.22/1.66  tff(c_32, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.22/1.66  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.66  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.22/1.66  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.22/1.66  tff(c_68, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.66  tff(c_76, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_68])).
% 3.22/1.66  tff(c_28, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.22/1.66  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.66  tff(c_173, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, k3_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.66  tff(c_207, plain, (![A_48, B_49]: (~r1_xboole_0(A_48, B_49) | k3_xboole_0(A_48, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_173])).
% 3.22/1.66  tff(c_222, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_207])).
% 3.22/1.66  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.22/1.66  tff(c_357, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_222, c_18])).
% 3.22/1.66  tff(c_364, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_357])).
% 3.22/1.66  tff(c_22, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.66  tff(c_537, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k3_xboole_0(A_60, B_61), k3_xboole_0(A_60, C_62))=k3_xboole_0(A_60, k4_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.66  tff(c_1586, plain, (![A_82, B_83, C_84]: (k3_xboole_0(A_82, k4_xboole_0(B_83, k3_xboole_0(A_82, C_84)))=k3_xboole_0(A_82, k4_xboole_0(B_83, C_84)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_537])).
% 3.22/1.66  tff(c_1717, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_364, c_1586])).
% 3.22/1.66  tff(c_1784, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_76, c_1717])).
% 3.22/1.66  tff(c_26, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.66  tff(c_186, plain, (![A_12, C_44]: (~r1_xboole_0(A_12, k1_xboole_0) | ~r2_hidden(C_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_173])).
% 3.22/1.66  tff(c_189, plain, (![C_44]: (~r2_hidden(C_44, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_186])).
% 3.22/1.66  tff(c_455, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(A_57, k4_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.66  tff(c_81, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.66  tff(c_99, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_81])).
% 3.22/1.66  tff(c_103, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_99])).
% 3.22/1.66  tff(c_622, plain, (![A_63, B_64]: (k3_xboole_0(A_63, k4_xboole_0(B_64, k3_xboole_0(A_63, B_64)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_455, c_103])).
% 3.22/1.66  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.66  tff(c_642, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, k4_xboole_0(B_64, k3_xboole_0(A_63, B_64))), k1_xboole_0) | r1_xboole_0(A_63, k4_xboole_0(B_64, k3_xboole_0(A_63, B_64))))), inference(superposition, [status(thm), theory('equality')], [c_622, c_4])).
% 3.22/1.66  tff(c_874, plain, (![A_66, B_67]: (r1_xboole_0(A_66, k4_xboole_0(B_67, k3_xboole_0(A_66, B_67))))), inference(negUnitSimplification, [status(thm)], [c_189, c_642])).
% 3.22/1.66  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.66  tff(c_930, plain, (![B_67, A_66]: (r1_xboole_0(k4_xboole_0(B_67, k3_xboole_0(A_66, B_67)), A_66))), inference(resolution, [status(thm)], [c_874, c_2])).
% 3.22/1.66  tff(c_1800, plain, (r1_xboole_0(k4_xboole_0('#skF_3', k1_xboole_0), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1784, c_930])).
% 3.22/1.66  tff(c_1831, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1800])).
% 3.22/1.66  tff(c_1833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1831])).
% 3.22/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.66  
% 3.22/1.66  Inference rules
% 3.22/1.66  ----------------------
% 3.22/1.66  #Ref     : 0
% 3.22/1.66  #Sup     : 444
% 3.22/1.66  #Fact    : 0
% 3.22/1.66  #Define  : 0
% 3.22/1.66  #Split   : 1
% 3.22/1.66  #Chain   : 0
% 3.22/1.66  #Close   : 0
% 3.22/1.66  
% 3.22/1.66  Ordering : KBO
% 3.22/1.66  
% 3.22/1.66  Simplification rules
% 3.22/1.66  ----------------------
% 3.22/1.66  #Subsume      : 10
% 3.22/1.66  #Demod        : 420
% 3.22/1.66  #Tautology    : 292
% 3.22/1.66  #SimpNegUnit  : 11
% 3.22/1.66  #BackRed      : 0
% 3.22/1.66  
% 3.22/1.66  #Partial instantiations: 0
% 3.22/1.66  #Strategies tried      : 1
% 3.22/1.66  
% 3.22/1.66  Timing (in seconds)
% 3.22/1.66  ----------------------
% 3.39/1.66  Preprocessing        : 0.32
% 3.39/1.66  Parsing              : 0.18
% 3.39/1.66  CNF conversion       : 0.02
% 3.39/1.66  Main loop            : 0.47
% 3.39/1.66  Inferencing          : 0.16
% 3.39/1.66  Reduction            : 0.19
% 3.39/1.66  Demodulation         : 0.15
% 3.39/1.66  BG Simplification    : 0.02
% 3.39/1.66  Subsumption          : 0.06
% 3.39/1.66  Abstraction          : 0.03
% 3.39/1.66  MUC search           : 0.00
% 3.39/1.66  Cooper               : 0.00
% 3.39/1.66  Total                : 0.82
% 3.39/1.66  Index Insertion      : 0.00
% 3.39/1.66  Index Deletion       : 0.00
% 3.39/1.66  Index Matching       : 0.00
% 3.39/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
