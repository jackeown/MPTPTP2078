%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:28 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 114 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 214 expanded)
%              Number of equality atoms :   58 ( 136 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_45,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_45])).

tff(c_12,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_182,plain,(
    ! [B_50,C_51,A_52] :
      ( k2_tarski(B_50,C_51) = A_52
      | k1_tarski(C_51) = A_52
      | k1_tarski(B_50) = A_52
      | k1_xboole_0 = A_52
      | ~ r1_tarski(A_52,k2_tarski(B_50,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_191,plain,(
    ! [A_8,A_52] :
      ( k2_tarski(A_8,A_8) = A_52
      | k1_tarski(A_8) = A_52
      | k1_tarski(A_8) = A_52
      | k1_xboole_0 = A_52
      | ~ r1_tarski(A_52,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_182])).

tff(c_480,plain,(
    ! [A_73,A_74] :
      ( k1_tarski(A_73) = A_74
      | k1_tarski(A_73) = A_74
      | k1_tarski(A_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(A_73)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_191])).

tff(c_489,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_480])).

tff(c_499,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_489])).

tff(c_117,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_117])).

tff(c_146,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_508,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_146])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_508])).

tff(c_515,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_518,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_36])).

tff(c_576,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(A_76,k2_xboole_0(C_77,B_78))
      | ~ r1_tarski(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_584,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,'#skF_2')
      | ~ r1_tarski(A_76,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_576])).

tff(c_669,plain,(
    ! [B_90,C_91,A_92] :
      ( k2_tarski(B_90,C_91) = A_92
      | k1_tarski(C_91) = A_92
      | k1_tarski(B_90) = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,k2_tarski(B_90,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_684,plain,(
    ! [A_8,A_92] :
      ( k2_tarski(A_8,A_8) = A_92
      | k1_tarski(A_8) = A_92
      | k1_tarski(A_8) = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_669])).

tff(c_1125,plain,(
    ! [A_121,A_122] :
      ( k1_tarski(A_121) = A_122
      | k1_tarski(A_121) = A_122
      | k1_tarski(A_121) = A_122
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,k1_tarski(A_121)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_684])).

tff(c_1128,plain,(
    ! [A_122] :
      ( k1_tarski('#skF_1') = A_122
      | k1_tarski('#skF_1') = A_122
      | k1_tarski('#skF_1') = A_122
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_1125])).

tff(c_1141,plain,(
    ! [A_123] :
      ( A_123 = '#skF_2'
      | A_123 = '#skF_2'
      | A_123 = '#skF_2'
      | k1_xboole_0 = A_123
      | ~ r1_tarski(A_123,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_515,c_515,c_1128])).

tff(c_1161,plain,(
    ! [A_124] :
      ( A_124 = '#skF_2'
      | k1_xboole_0 = A_124
      | ~ r1_tarski(A_124,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_584,c_1141])).

tff(c_1165,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_1161])).

tff(c_1169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_34,c_1165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.45  
% 2.74/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.45  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.45  
% 2.74/1.45  %Foreground sorts:
% 2.74/1.45  
% 2.74/1.45  
% 2.74/1.45  %Background operators:
% 2.74/1.45  
% 2.74/1.45  
% 2.74/1.45  %Foreground operators:
% 2.74/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.74/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.45  
% 3.16/1.46  tff(f_73, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.16/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.46  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.16/1.46  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.16/1.46  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.16/1.46  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.16/1.46  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.46  tff(c_34, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.46  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.46  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.46  tff(c_45, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.46  tff(c_48, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_45])).
% 3.16/1.46  tff(c_12, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.46  tff(c_182, plain, (![B_50, C_51, A_52]: (k2_tarski(B_50, C_51)=A_52 | k1_tarski(C_51)=A_52 | k1_tarski(B_50)=A_52 | k1_xboole_0=A_52 | ~r1_tarski(A_52, k2_tarski(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.46  tff(c_191, plain, (![A_8, A_52]: (k2_tarski(A_8, A_8)=A_52 | k1_tarski(A_8)=A_52 | k1_tarski(A_8)=A_52 | k1_xboole_0=A_52 | ~r1_tarski(A_52, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_182])).
% 3.16/1.46  tff(c_480, plain, (![A_73, A_74]: (k1_tarski(A_73)=A_74 | k1_tarski(A_73)=A_74 | k1_tarski(A_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_191])).
% 3.16/1.46  tff(c_489, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_48, c_480])).
% 3.16/1.46  tff(c_499, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32, c_489])).
% 3.16/1.46  tff(c_117, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.46  tff(c_138, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_48, c_117])).
% 3.16/1.46  tff(c_146, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_138])).
% 3.16/1.46  tff(c_508, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_146])).
% 3.16/1.46  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_508])).
% 3.16/1.46  tff(c_515, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_138])).
% 3.16/1.46  tff(c_518, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_515, c_36])).
% 3.16/1.46  tff(c_576, plain, (![A_76, C_77, B_78]: (r1_tarski(A_76, k2_xboole_0(C_77, B_78)) | ~r1_tarski(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.46  tff(c_584, plain, (![A_76]: (r1_tarski(A_76, '#skF_2') | ~r1_tarski(A_76, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_518, c_576])).
% 3.16/1.46  tff(c_669, plain, (![B_90, C_91, A_92]: (k2_tarski(B_90, C_91)=A_92 | k1_tarski(C_91)=A_92 | k1_tarski(B_90)=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, k2_tarski(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.46  tff(c_684, plain, (![A_8, A_92]: (k2_tarski(A_8, A_8)=A_92 | k1_tarski(A_8)=A_92 | k1_tarski(A_8)=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_669])).
% 3.16/1.46  tff(c_1125, plain, (![A_121, A_122]: (k1_tarski(A_121)=A_122 | k1_tarski(A_121)=A_122 | k1_tarski(A_121)=A_122 | k1_xboole_0=A_122 | ~r1_tarski(A_122, k1_tarski(A_121)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_684])).
% 3.16/1.46  tff(c_1128, plain, (![A_122]: (k1_tarski('#skF_1')=A_122 | k1_tarski('#skF_1')=A_122 | k1_tarski('#skF_1')=A_122 | k1_xboole_0=A_122 | ~r1_tarski(A_122, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_515, c_1125])).
% 3.16/1.46  tff(c_1141, plain, (![A_123]: (A_123='#skF_2' | A_123='#skF_2' | A_123='#skF_2' | k1_xboole_0=A_123 | ~r1_tarski(A_123, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_515, c_515, c_1128])).
% 3.16/1.46  tff(c_1161, plain, (![A_124]: (A_124='#skF_2' | k1_xboole_0=A_124 | ~r1_tarski(A_124, '#skF_3'))), inference(resolution, [status(thm)], [c_584, c_1141])).
% 3.16/1.46  tff(c_1165, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_1161])).
% 3.16/1.46  tff(c_1169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_34, c_1165])).
% 3.16/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.46  
% 3.16/1.46  Inference rules
% 3.16/1.46  ----------------------
% 3.16/1.46  #Ref     : 0
% 3.16/1.46  #Sup     : 241
% 3.16/1.46  #Fact    : 0
% 3.16/1.46  #Define  : 0
% 3.16/1.46  #Split   : 6
% 3.16/1.46  #Chain   : 0
% 3.16/1.46  #Close   : 0
% 3.16/1.46  
% 3.16/1.46  Ordering : KBO
% 3.16/1.46  
% 3.16/1.46  Simplification rules
% 3.16/1.46  ----------------------
% 3.16/1.46  #Subsume      : 48
% 3.16/1.46  #Demod        : 109
% 3.16/1.46  #Tautology    : 71
% 3.16/1.46  #SimpNegUnit  : 8
% 3.16/1.46  #BackRed      : 11
% 3.16/1.46  
% 3.16/1.46  #Partial instantiations: 0
% 3.16/1.46  #Strategies tried      : 1
% 3.16/1.46  
% 3.16/1.46  Timing (in seconds)
% 3.16/1.46  ----------------------
% 3.16/1.46  Preprocessing        : 0.29
% 3.16/1.46  Parsing              : 0.15
% 3.16/1.46  CNF conversion       : 0.02
% 3.16/1.46  Main loop            : 0.41
% 3.16/1.46  Inferencing          : 0.14
% 3.16/1.46  Reduction            : 0.14
% 3.16/1.46  Demodulation         : 0.10
% 3.16/1.46  BG Simplification    : 0.02
% 3.16/1.46  Subsumption          : 0.09
% 3.16/1.46  Abstraction          : 0.02
% 3.16/1.47  MUC search           : 0.00
% 3.16/1.47  Cooper               : 0.00
% 3.16/1.47  Total                : 0.72
% 3.16/1.47  Index Insertion      : 0.00
% 3.16/1.47  Index Deletion       : 0.00
% 3.16/1.47  Index Matching       : 0.00
% 3.16/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
