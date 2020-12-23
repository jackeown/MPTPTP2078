%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:57 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   49 (  75 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 ( 139 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

tff(c_26,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v3_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_37,plain,(
    ~ v3_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [B_14] :
      ( v3_relat_1('#skF_4')
      | k1_xboole_0 = B_14
      | ~ r2_hidden(B_14,k2_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_53,plain,(
    ! [B_20] :
      ( k1_xboole_0 = B_20
      | ~ r2_hidden(B_20,k2_relat_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_36])).

tff(c_107,plain,(
    ! [B_35] :
      ( '#skF_1'(k2_relat_1('#skF_4'),B_35) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_4'),B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_20,plain,(
    ! [A_11] :
      ( v3_relat_1(A_11)
      | ~ r1_tarski(k2_relat_1(A_11),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,
    ( v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_20])).

tff(c_114,plain,
    ( v3_relat_1('#skF_4')
    | '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_111])).

tff(c_115,plain,(
    '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_114])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_4])).

tff(c_126,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_119])).

tff(c_130,plain,
    ( v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_20])).

tff(c_133,plain,(
    v3_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_130])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_133])).

tff(c_136,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_137,plain,(
    v3_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_22,plain,(
    ! [A_11] :
      ( r1_tarski(k2_relat_1(A_11),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_4'))
    | ~ v3_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_140,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_28])).

tff(c_168,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [B_49] :
      ( r2_hidden('#skF_5',B_49)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_49) ) ),
    inference(resolution,[status(thm)],[c_140,c_168])).

tff(c_182,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_178])).

tff(c_189,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_137,c_182])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_196,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_189,c_8])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  %$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 1.95/1.25  
% 1.95/1.25  %Foreground sorts:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Background operators:
% 1.95/1.25  
% 1.95/1.25  
% 1.95/1.25  %Foreground operators:
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.25  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 1.95/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.95/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.95/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.25  
% 1.95/1.26  tff(f_55, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 1.95/1.26  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.95/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.95/1.26  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_relat_1)).
% 1.95/1.26  tff(c_26, plain, (k1_xboole_0!='#skF_5' | ~v3_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.26  tff(c_37, plain, (~v3_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 1.95/1.26  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.26  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.26  tff(c_36, plain, (![B_14]: (v3_relat_1('#skF_4') | k1_xboole_0=B_14 | ~r2_hidden(B_14, k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.26  tff(c_53, plain, (![B_20]: (k1_xboole_0=B_20 | ~r2_hidden(B_20, k2_relat_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_37, c_36])).
% 1.95/1.26  tff(c_107, plain, (![B_35]: ('#skF_1'(k2_relat_1('#skF_4'), B_35)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_4'), B_35))), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.95/1.26  tff(c_20, plain, (![A_11]: (v3_relat_1(A_11) | ~r1_tarski(k2_relat_1(A_11), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.26  tff(c_111, plain, (v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_107, c_20])).
% 1.95/1.26  tff(c_114, plain, (v3_relat_1('#skF_4') | '#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_111])).
% 1.95/1.26  tff(c_115, plain, ('#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_37, c_114])).
% 1.95/1.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.26  tff(c_119, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_4])).
% 1.95/1.26  tff(c_126, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_119])).
% 1.95/1.26  tff(c_130, plain, (v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_126, c_20])).
% 1.95/1.26  tff(c_133, plain, (v3_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_130])).
% 1.95/1.26  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_133])).
% 1.95/1.26  tff(c_136, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_26])).
% 1.95/1.26  tff(c_137, plain, (v3_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 1.95/1.26  tff(c_22, plain, (![A_11]: (r1_tarski(k2_relat_1(A_11), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.26  tff(c_28, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~v3_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.26  tff(c_140, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_28])).
% 1.95/1.26  tff(c_168, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.26  tff(c_178, plain, (![B_49]: (r2_hidden('#skF_5', B_49) | ~r1_tarski(k2_relat_1('#skF_4'), B_49))), inference(resolution, [status(thm)], [c_140, c_168])).
% 1.95/1.26  tff(c_182, plain, (r2_hidden('#skF_5', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_178])).
% 1.95/1.26  tff(c_189, plain, (r2_hidden('#skF_5', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_137, c_182])).
% 1.95/1.26  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.26  tff(c_196, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_189, c_8])).
% 1.95/1.26  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_196])).
% 1.95/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  
% 1.95/1.26  Inference rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Ref     : 0
% 1.95/1.26  #Sup     : 30
% 1.95/1.26  #Fact    : 0
% 1.95/1.26  #Define  : 0
% 1.95/1.26  #Split   : 2
% 1.95/1.26  #Chain   : 0
% 1.95/1.26  #Close   : 0
% 1.95/1.26  
% 1.95/1.26  Ordering : KBO
% 1.95/1.26  
% 1.95/1.26  Simplification rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Subsume      : 3
% 1.95/1.26  #Demod        : 11
% 1.95/1.26  #Tautology    : 15
% 1.95/1.26  #SimpNegUnit  : 4
% 1.95/1.26  #BackRed      : 0
% 1.95/1.26  
% 1.95/1.26  #Partial instantiations: 0
% 1.95/1.26  #Strategies tried      : 1
% 1.95/1.26  
% 1.95/1.26  Timing (in seconds)
% 1.95/1.26  ----------------------
% 1.95/1.27  Preprocessing        : 0.30
% 1.95/1.27  Parsing              : 0.15
% 1.95/1.27  CNF conversion       : 0.03
% 1.95/1.27  Main loop            : 0.15
% 1.95/1.27  Inferencing          : 0.05
% 1.95/1.27  Reduction            : 0.04
% 1.95/1.27  Demodulation         : 0.03
% 1.95/1.27  BG Simplification    : 0.01
% 1.95/1.27  Subsumption          : 0.03
% 1.95/1.27  Abstraction          : 0.01
% 1.95/1.27  MUC search           : 0.00
% 1.95/1.27  Cooper               : 0.00
% 1.95/1.27  Total                : 0.48
% 1.95/1.27  Index Insertion      : 0.00
% 1.95/1.27  Index Deletion       : 0.00
% 1.95/1.27  Index Matching       : 0.00
% 1.95/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
