%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:28 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   59 (  76 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 111 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_159,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_168,plain,(
    ! [A_18,C_38] :
      ( ~ r1_xboole_0(A_18,k1_xboole_0)
      | ~ r2_hidden(C_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_159])).

tff(c_181,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_168])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_224,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_xboole_0(A_41,C_42)
      | ~ r1_xboole_0(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_244,plain,(
    ! [A_44] :
      ( r1_xboole_0(A_44,'#skF_5')
      | ~ r1_tarski(A_44,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_224])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_410,plain,(
    ! [A_64] :
      ( k3_xboole_0(A_64,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_414,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_410])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_418,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_5'),k1_xboole_0)
    | r1_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_8])).

tff(c_424,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_418])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_436,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_424,c_6])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,C_17)
      | ~ r1_xboole_0(B_16,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_492,plain,(
    ! [A_67] :
      ( r1_xboole_0(A_67,'#skF_3')
      | ~ r1_tarski(A_67,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_436,c_18])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_119,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_134,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_119])).

tff(c_138,plain,(
    ! [A_35] : k4_xboole_0(A_35,A_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_134])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    ! [A_35] : k4_xboole_0(A_35,k1_xboole_0) = k3_xboole_0(A_35,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_16])).

tff(c_192,plain,(
    ! [A_40] : k3_xboole_0(A_40,A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_143])).

tff(c_10,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_198,plain,(
    ! [A_40,C_9] :
      ( ~ r1_xboole_0(A_40,A_40)
      | ~ r2_hidden(C_9,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_10])).

tff(c_495,plain,(
    ! [C_9] :
      ( ~ r2_hidden(C_9,'#skF_3')
      | ~ r1_tarski('#skF_3','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_492,c_198])).

tff(c_509,plain,(
    ! [C_68] : ~ r2_hidden(C_68,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_495])).

tff(c_513,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12,c_509])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.84  
% 2.81/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.81/1.85  
% 2.81/1.85  %Foreground sorts:
% 2.81/1.85  
% 2.81/1.85  
% 2.81/1.85  %Background operators:
% 2.81/1.85  
% 2.81/1.85  
% 2.81/1.85  %Foreground operators:
% 2.81/1.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.81/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.85  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.85  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.85  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.85  
% 3.16/1.87  tff(f_76, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 3.16/1.87  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.16/1.87  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.16/1.87  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.16/1.87  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.16/1.87  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.16/1.87  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.16/1.87  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.16/1.87  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.16/1.87  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.87  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.87  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.87  tff(c_20, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/1.87  tff(c_56, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.87  tff(c_72, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_56])).
% 3.16/1.87  tff(c_159, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.16/1.87  tff(c_168, plain, (![A_18, C_38]: (~r1_xboole_0(A_18, k1_xboole_0) | ~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72, c_159])).
% 3.16/1.87  tff(c_181, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_168])).
% 3.16/1.87  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.87  tff(c_24, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.87  tff(c_224, plain, (![A_41, C_42, B_43]: (r1_xboole_0(A_41, C_42) | ~r1_xboole_0(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.87  tff(c_244, plain, (![A_44]: (r1_xboole_0(A_44, '#skF_5') | ~r1_tarski(A_44, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_224])).
% 3.16/1.87  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.87  tff(c_410, plain, (![A_64]: (k3_xboole_0(A_64, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_244, c_2])).
% 3.16/1.87  tff(c_414, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_410])).
% 3.16/1.87  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.16/1.87  tff(c_418, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_5'), k1_xboole_0) | r1_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_414, c_8])).
% 3.16/1.87  tff(c_424, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_181, c_418])).
% 3.16/1.87  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.87  tff(c_436, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_424, c_6])).
% 3.16/1.87  tff(c_18, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, C_17) | ~r1_xboole_0(B_16, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.87  tff(c_492, plain, (![A_67]: (r1_xboole_0(A_67, '#skF_3') | ~r1_tarski(A_67, '#skF_5'))), inference(resolution, [status(thm)], [c_436, c_18])).
% 3.16/1.87  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.87  tff(c_119, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.16/1.87  tff(c_134, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_119])).
% 3.16/1.87  tff(c_138, plain, (![A_35]: (k4_xboole_0(A_35, A_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_134])).
% 3.16/1.87  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.16/1.87  tff(c_143, plain, (![A_35]: (k4_xboole_0(A_35, k1_xboole_0)=k3_xboole_0(A_35, A_35))), inference(superposition, [status(thm), theory('equality')], [c_138, c_16])).
% 3.16/1.87  tff(c_192, plain, (![A_40]: (k3_xboole_0(A_40, A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_143])).
% 3.16/1.87  tff(c_10, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.16/1.87  tff(c_198, plain, (![A_40, C_9]: (~r1_xboole_0(A_40, A_40) | ~r2_hidden(C_9, A_40))), inference(superposition, [status(thm), theory('equality')], [c_192, c_10])).
% 3.16/1.87  tff(c_495, plain, (![C_9]: (~r2_hidden(C_9, '#skF_3') | ~r1_tarski('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_492, c_198])).
% 3.16/1.87  tff(c_509, plain, (![C_68]: (~r2_hidden(C_68, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_495])).
% 3.16/1.87  tff(c_513, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_12, c_509])).
% 3.16/1.87  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_513])).
% 3.16/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.87  
% 3.16/1.87  Inference rules
% 3.16/1.87  ----------------------
% 3.16/1.87  #Ref     : 0
% 3.16/1.87  #Sup     : 121
% 3.16/1.87  #Fact    : 0
% 3.16/1.87  #Define  : 0
% 3.16/1.87  #Split   : 2
% 3.16/1.87  #Chain   : 0
% 3.16/1.87  #Close   : 0
% 3.16/1.87  
% 3.16/1.87  Ordering : KBO
% 3.16/1.87  
% 3.16/1.87  Simplification rules
% 3.16/1.87  ----------------------
% 3.16/1.87  #Subsume      : 18
% 3.16/1.87  #Demod        : 20
% 3.16/1.87  #Tautology    : 42
% 3.16/1.87  #SimpNegUnit  : 7
% 3.16/1.87  #BackRed      : 0
% 3.16/1.87  
% 3.16/1.87  #Partial instantiations: 0
% 3.16/1.87  #Strategies tried      : 1
% 3.16/1.87  
% 3.16/1.87  Timing (in seconds)
% 3.16/1.87  ----------------------
% 3.16/1.87  Preprocessing        : 0.45
% 3.16/1.87  Parsing              : 0.24
% 3.16/1.88  CNF conversion       : 0.03
% 3.16/1.88  Main loop            : 0.44
% 3.16/1.88  Inferencing          : 0.17
% 3.16/1.88  Reduction            : 0.12
% 3.16/1.88  Demodulation         : 0.09
% 3.16/1.88  BG Simplification    : 0.02
% 3.16/1.88  Subsumption          : 0.09
% 3.16/1.88  Abstraction          : 0.02
% 3.16/1.88  MUC search           : 0.00
% 3.16/1.88  Cooper               : 0.00
% 3.16/1.88  Total                : 0.95
% 3.16/1.88  Index Insertion      : 0.00
% 3.16/1.88  Index Deletion       : 0.00
% 3.16/1.88  Index Matching       : 0.00
% 3.16/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
