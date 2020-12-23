%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:17 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 106 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_77,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_44,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [B_22,A_21] :
      ( r1_xboole_0(B_22,k1_tarski(A_21))
      | r2_hidden(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_147,plain,(
    ! [B_46,A_47] :
      ( k9_relat_1(B_46,A_47) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_46),A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_204,plain,(
    ! [B_55,A_56] :
      ( k9_relat_1(B_55,k1_tarski(A_56)) = k1_xboole_0
      | ~ v1_relat_1(B_55)
      | r2_hidden(A_56,k1_relat_1(B_55)) ) ),
    inference(resolution,[status(thm)],[c_47,c_147])).

tff(c_26,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_26])).

tff(c_207,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_204,c_78])).

tff(c_210,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_207])).

tff(c_18,plain,(
    ! [A_11,B_13] :
      ( k9_relat_1(A_11,k1_tarski(B_13)) = k11_relat_1(A_11,B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_220,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_18])).

tff(c_227,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_220])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_227])).

tff(c_231,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_230,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_297,plain,(
    ! [B_70,A_71] :
      ( r1_xboole_0(k1_relat_1(B_70),A_71)
      | k9_relat_1(B_70,A_71) != k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_390,plain,(
    ! [B_87,A_88] :
      ( k4_xboole_0(k1_relat_1(B_87),A_88) = k1_relat_1(B_87)
      | k9_relat_1(B_87,A_88) != k1_xboole_0
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_297,c_4])).

tff(c_14,plain,(
    ! [C_10,B_9] : ~ r2_hidden(C_10,k4_xboole_0(B_9,k1_tarski(C_10))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_454,plain,(
    ! [C_91,B_92] :
      ( ~ r2_hidden(C_91,k1_relat_1(B_92))
      | k9_relat_1(B_92,k1_tarski(C_91)) != k1_xboole_0
      | ~ v1_relat_1(B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_14])).

tff(c_460,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_230,c_454])).

tff(c_464,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_460])).

tff(c_467,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_464])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_231,c_467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:27:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.73  
% 2.63/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.73  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.63/1.73  
% 2.63/1.73  %Foreground sorts:
% 2.63/1.73  
% 2.63/1.73  
% 2.63/1.73  %Background operators:
% 2.63/1.73  
% 2.63/1.73  
% 2.63/1.73  %Foreground operators:
% 2.63/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.73  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.63/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.73  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.73  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.63/1.73  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.73  
% 2.63/1.75  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.63/1.75  tff(f_40, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.63/1.75  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.63/1.75  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.63/1.75  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.63/1.75  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.63/1.75  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.63/1.75  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.63/1.75  tff(c_32, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.63/1.75  tff(c_77, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.63/1.75  tff(c_44, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.63/1.75  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.75  tff(c_47, plain, (![B_22, A_21]: (r1_xboole_0(B_22, k1_tarski(A_21)) | r2_hidden(A_21, B_22))), inference(resolution, [status(thm)], [c_44, c_2])).
% 2.63/1.75  tff(c_147, plain, (![B_46, A_47]: (k9_relat_1(B_46, A_47)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_46), A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.63/1.75  tff(c_204, plain, (![B_55, A_56]: (k9_relat_1(B_55, k1_tarski(A_56))=k1_xboole_0 | ~v1_relat_1(B_55) | r2_hidden(A_56, k1_relat_1(B_55)))), inference(resolution, [status(thm)], [c_47, c_147])).
% 2.63/1.75  tff(c_26, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.63/1.75  tff(c_78, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_77, c_26])).
% 2.63/1.75  tff(c_207, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_204, c_78])).
% 2.63/1.75  tff(c_210, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_207])).
% 2.63/1.75  tff(c_18, plain, (![A_11, B_13]: (k9_relat_1(A_11, k1_tarski(B_13))=k11_relat_1(A_11, B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.75  tff(c_220, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_210, c_18])).
% 2.63/1.75  tff(c_227, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_220])).
% 2.63/1.75  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_227])).
% 2.63/1.75  tff(c_231, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.63/1.75  tff(c_230, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 2.63/1.75  tff(c_297, plain, (![B_70, A_71]: (r1_xboole_0(k1_relat_1(B_70), A_71) | k9_relat_1(B_70, A_71)!=k1_xboole_0 | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.63/1.75  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.75  tff(c_390, plain, (![B_87, A_88]: (k4_xboole_0(k1_relat_1(B_87), A_88)=k1_relat_1(B_87) | k9_relat_1(B_87, A_88)!=k1_xboole_0 | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_297, c_4])).
% 2.63/1.75  tff(c_14, plain, (![C_10, B_9]: (~r2_hidden(C_10, k4_xboole_0(B_9, k1_tarski(C_10))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.75  tff(c_454, plain, (![C_91, B_92]: (~r2_hidden(C_91, k1_relat_1(B_92)) | k9_relat_1(B_92, k1_tarski(C_91))!=k1_xboole_0 | ~v1_relat_1(B_92))), inference(superposition, [status(thm), theory('equality')], [c_390, c_14])).
% 2.63/1.75  tff(c_460, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_230, c_454])).
% 2.63/1.75  tff(c_464, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_460])).
% 2.63/1.75  tff(c_467, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_464])).
% 2.63/1.75  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_231, c_467])).
% 2.63/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.75  
% 2.63/1.75  Inference rules
% 2.63/1.75  ----------------------
% 2.63/1.75  #Ref     : 0
% 2.63/1.75  #Sup     : 97
% 2.63/1.75  #Fact    : 0
% 2.63/1.75  #Define  : 0
% 2.63/1.75  #Split   : 1
% 2.63/1.75  #Chain   : 0
% 2.63/1.75  #Close   : 0
% 2.63/1.75  
% 2.63/1.75  Ordering : KBO
% 2.63/1.75  
% 2.63/1.75  Simplification rules
% 2.63/1.75  ----------------------
% 2.63/1.75  #Subsume      : 12
% 2.63/1.75  #Demod        : 7
% 2.63/1.75  #Tautology    : 56
% 2.63/1.75  #SimpNegUnit  : 2
% 2.63/1.75  #BackRed      : 0
% 2.63/1.75  
% 2.63/1.75  #Partial instantiations: 0
% 2.63/1.75  #Strategies tried      : 1
% 2.63/1.75  
% 2.63/1.75  Timing (in seconds)
% 2.63/1.75  ----------------------
% 2.63/1.76  Preprocessing        : 0.47
% 2.63/1.76  Parsing              : 0.24
% 2.63/1.76  CNF conversion       : 0.03
% 2.63/1.76  Main loop            : 0.38
% 2.63/1.76  Inferencing          : 0.16
% 2.63/1.76  Reduction            : 0.09
% 2.63/1.76  Demodulation         : 0.05
% 2.63/1.76  BG Simplification    : 0.02
% 2.63/1.76  Subsumption          : 0.07
% 2.63/1.76  Abstraction          : 0.02
% 2.63/1.76  MUC search           : 0.00
% 2.63/1.76  Cooper               : 0.00
% 2.63/1.76  Total                : 0.89
% 2.63/1.76  Index Insertion      : 0.00
% 2.63/1.76  Index Deletion       : 0.00
% 2.63/1.76  Index Matching       : 0.00
% 2.63/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
